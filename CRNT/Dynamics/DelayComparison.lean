import CRNT.Dynamics.DelayExistence
import CRNT.Dynamics.MonotoneComparison
import CRNT.Dynamics.Gronwall

/-!
# The comparison principle for delay equations

This module proves the **classical comparison principle for delay differential equations**: if
`x` and `y` are two solutions of the *same* delay equation

`ẋ(t) = F.f ( t, x(t), x(t - τ) )`,   `τ > 0`,

with the *same* delay `τ`, with *ordered* histories (`x t ≤ y t` for `t ≤ 0`), and if the right-hand
side `F.f` is **monotone** (nondecreasing in the current state and in the delayed state), then

`x t ≤ y t`   for every `t ≥ 0`.

Reference: J. K. Hale, *Ordinary Differential Equations*, Wiley 1980, Chapter 5 ("Comparison
theorems"); see also A. A. Halanay, *Differential Equations and Applications*, 1983, Chapter 3.
The proof is the classical **method of steps**, which the repository already implements for the
*existence* of delay solutions in `CRNT.Dynamics.DelayExistence`; here the method of steps is used
for the *comparison* of two delay solutions.

## The two towers of the delay content of the repository

The delay content of the repository comes in two *disjoint* towers, and this module works in the
first one only:

* the **general Banach-space delay field** `CRNT.Dynamics.DelayField`, with the solutions
  `CRNT.Dynamics.DelaySolutionOn` and the predicate `CRNT.Dynamics.IsDelaySolutionOn`; this is
  the tower of `CRNT.Dynamics.DelayExistence` (existence and uniqueness by the method of steps)
  and of `CRNT.Dynamics.DelayHalanay` (the Halanay inequality and the semistability of the linear
  delay equation);
* the **mass-action delay system** `CRNT.Network.IsDelaySolution` of
  `CRNT/Extensions/DelayMassAction.lean`, i.e. the systems
  `ẋ(t) = ∑_r κ_r ( x(t - τ_r)^{y_r} y'_r - x(t)^{y_r} y_r )` of
  Lipták–Hangos–Pituk–Szederkényi.

The two towers do not meet: the mass-action delay system is a *specific* vector field on
`ℝ^S`, not an element of the general `DelayField` structure (the general tower works with an
arbitrary Banach space and an arbitrary right-hand side).  Everything below is stated for the
first tower.

## The comparison principle and the Halanay estimate

The two results of the first tower are complementary:

* the **Halanay estimate** of `CRNT.Dynamics.DelayHalanay` is a *decay* statement: it bounds the
  size of a solution of a scalar *delay inequality* by an exponential;
* the **comparison principle** of this module is an *order* statement: it says that the delay flow
  preserves the order of the histories.

The comparison principle is the tool that transports the Halanay estimate to the nonlinear case:
if `x` is a solution and `w` a supersolution of the same (scalar) delay equation, then
`x ≤ w` on the whole half line, provided `w` dominates the history of `x` (this is
`delay_comparison_difference`).

## The content of this module

* `delay_comparison_step`: the one-step comparison lemma for ordinary differential equations
  (a subsolution below a solution), the ingredient of the method of steps;
* `delay_comparison_subsolution`, `delay_comparison_scalar`: **the comparison principle**, in the
  scalar setting `E = ℝ`; the second is the classical statement (two solutions of the same delay
  equation with ordered histories are ordered), the first the subsolution version;
* `delay_comparison_on`, `delay_comparison_global`: the same statement for the solutions of
  `CRNT.Dynamics.DelayExistence` (on a finite interval and on the half line);
* `delay_comparison_difference`: the one-sided form, in terms of the difference of the two
  right-hand sides (the form used for supersolutions);
* `delay_comparison_eq`: the *order* version of uniqueness (two solutions with mutually ordered
  histories coincide);
* `delay_difference_sq_sub`, `delay_difference_exp_le`, `growth_rate_exists`: the **quantitative**
  form: the squared difference of two solutions satisfies the linear delay inequality
  `v' ≤ (2 K₂ + K₃) v(t) + K₃ v(t - τ)`, and hence grows at most exponentially with the rate `ε`
  solving `2 K₂ + K₃ + K₃ e^{-ε τ} = ε` (the existence of such a rate is `growth_rate_exists`).

## What is *not* proved here

* **The comparison principle in a general ordered Banach space.**  The proof above uses the
  *positive part* `t ↦ (max (x t - y t) 0)²` of the difference of the two trajectories; this
  requires the state space to carry a *lattice* structure (a componentwise order), which a general
  Banach space does not have.  The natural setting beyond `E = ℝ` is therefore the finite
  dimensional one, `E = ℝ^S` with the componentwise order, where the ordinary differential
  equation counterpart of the statement is `CRNT.Monotone.kamke_comparison`; the delay version of
  that statement (with the delayed part handled by the method of steps) is *not* proved here.
* The **comparison principle for the mass-action delay system** of
  `CRNT/Extensions/DelayMassAction.lean` is *not* proved here.  It would require the mass-action
  delay field to be monotone, which it is *not* in general: the mass-action field contains the
  monomials `x(t)^{y_r}`, which are only monotone on the nonnegative orthant, and the delayed
  species `x(t - τ_r)` enter with a *negative* sign in the consumption term.  The order-theoretic
  tools of `CRNT.Dynamics.MonotoneComparison` (the Kamke condition) are therefore not available
  for the mass-action delay systems.
* The **path-space (LaSalle) theory** of delay equations is not touched here.
* The case `τ = 0` (a *pure* ordinary differential equation) is not covered by the statement
  below: the delayed part then coincides with the current part, the right-hand side
  `u ↦ F.f t u u` is monotone but need not be Lipschitz, and the comparison principle for
  monotone (non-Lipschitz) ordinary differential equations is a separate classical result.
-/
namespace CRNT
namespace Dynamics

open Filter Topology Set
open scoped NNReal BigOperators

set_option maxHeartbeats 800000

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-! ### The one-step comparison lemma -/

/-- **The one-step comparison lemma (scalar version).**  Let `h : ℝ → ℝ → ℝ` be Lipschitz in its
second argument with constant `K`, let `x` be a *subsolution* of the ordinary differential equation
`u' = h (t, u)` and `y` a *solution* of it, and assume `x a ≤ y a`.  Then `x t ≤ y t` on
`[a, b]`.

This is the classical comparison principle for ordinary differential equations; it is the
ingredient of the method of steps below.  The proof is the standard one: the positive part
`V t = (max (x t - y t) 0)²` satisfies the differential inequality `V' ≤ 2 K V` with `V a = 0`,
hence `V ≡ 0`.

Only the Lipschitz bound is used; in particular the lemma applies to *subsolutions*, which is
what the delay equation needs (on a step, the delayed part of the subsolution is bounded by the
delayed part of the solution, and monotonicity turns the subsolution into a subsolution of the
ordinary differential equation with the *upper* delayed part fixed). -/
theorem delay_comparison_step {a b : ℝ} {h : ℝ → ℝ → ℝ} {K : ℝ≥0}
    (hlip : ∀ t, LipschitzWith K (fun u => h t u))
    {x y : ℝ → ℝ} {fx : ℝ → ℝ}
    (hx : ∀ t ∈ Set.Icc a b, HasDerivWithinAt x (fx t) (Set.Icc a b) t)
    (hsub : ∀ t ∈ Set.Icc a b, fx t ≤ h t (x t))
    (hy : ∀ t ∈ Set.Icc a b, HasDerivWithinAt y (h t (y t)) (Set.Icc a b) t)
    (ha : x a ≤ y a) :
    ∀ t ∈ Set.Icc a b, x t ≤ y t := by
  have hdx : ∀ t ∈ Set.Icc a b, HasDerivWithinAt (fun s => x s - y s)
      (fx t - h t (y t)) (Set.Icc a b) t := by
    intro t ht
    exact (hx t ht).sub (hy t ht)
  have hV : ∀ t ∈ Set.Icc a b, HasDerivWithinAt (fun s => (max (x s - y s) 0) ^ 2)
      (2 * max (x t - y t) 0 * (fx t - h t (y t))) (Set.Icc a b) t := by
    intro t ht
    exact (Monotone.hasDerivAt_posPart_sq (x t - y t)).comp_hasDerivWithinAt t (hdx t ht)
  -- the differential inequality `V' ≤ 2 K V`
  have hineq : ∀ t ∈ Set.Icc a b,
      2 * max (x t - y t) 0 * (fx t - h t (y t))
        ≤ 2 * (K : ℝ) * (max (x t - y t) 0) ^ 2 := by
    intro t ht
    by_cases hd : 0 < x t - y t
    · have hd' : max (x t - y t) 0 = x t - y t := max_eq_left hd.le
      rw [hd']
      have h1 : h t (x t) - h t (y t) ≤ (K : ℝ) * (x t - y t) := by
        have hdist := (hlip t).dist_le_mul (x t) (y t)
        rw [Real.dist_eq] at hdist
        rw [Real.dist_eq] at hdist
        have habs : |x t - y t| = x t - y t := abs_of_pos hd
        rw [habs] at hdist
        have h2 : h t (x t) - h t (y t) ≤ |h t (x t) - h t (y t)| := le_abs_self _
        linarith
      have h2 : 0 ≤ 2 * (x t - y t) := by linarith
      have h3 : fx t - h t (y t) ≤ (K : ℝ) * (x t - y t) := by linarith [hsub t ht]
      have h4 := mul_le_mul_of_nonneg_left h3 h2
      nlinarith [h4]
    · have hd' : max (x t - y t) 0 = 0 := max_eq_right (not_lt.mp hd)
      rw [hd']
      simp
  -- the auxiliary function `g t = exp (-2 K t) * V t` is nonincreasing
  have hexpderiv : ∀ c t : ℝ, HasDerivAt (fun s => Real.exp (c * s)) (c * Real.exp (c * t)) t := by
    intro c t
    have h1 := (Real.hasDerivAt_exp (c * t)).comp_of_eq t ((hasDerivAt_id t).const_mul c) rfl
    convert h1 using 1
    · funext s; rfl
    · ring
  set c : ℝ := -2 * (K : ℝ) with hcdef
  set g : ℝ → ℝ := fun t => Real.exp (c * t) * (max (x t - y t) 0) ^ 2 with hgdef
  have hg : ∀ t ∈ Set.Icc a b, HasDerivWithinAt g
      (Real.exp (c * t) * (2 * max (x t - y t) 0 * (fx t - h t (y t))
        + c * (max (x t - y t) 0) ^ 2)) (Set.Icc a b) t := by
    intro t ht
    have h1 := (hexpderiv c t).hasDerivWithinAt.mul (hV t ht)
    rw [hgdef]
    convert h1 using 1
    ring
  have hgcont : ContinuousOn g (Set.Icc a b) := by
    intro t ht
    exact (hg t ht).continuousWithinAt
  have hgderiv : ∀ t ∈ interior (Set.Icc a b),
      HasDerivWithinAt g
        (Real.exp (c * t) * (2 * max (x t - y t) 0 * (fx t - h t (y t))
          + c * (max (x t - y t) 0) ^ 2)) (interior (Set.Icc a b)) t := by
    intro t ht
    exact (hg t (interior_subset ht)).mono interior_subset
  have hgnonpos : ∀ t ∈ interior (Set.Icc a b),
      Real.exp (c * t) * (2 * max (x t - y t) 0 * (fx t - h t (y t))
        + c * (max (x t - y t) 0) ^ 2) ≤ 0 := by
    intro t ht
    have h1 := hineq t (interior_subset ht)
    have h3 : c = -2 * (K : ℝ) := by rw [hcdef]
    rw [h3]
    have hX : 2 * max (x t - y t) 0 * (fx t - h t (y t))
        + (-2 * (K : ℝ)) * (max (x t - y t) 0) ^ 2 ≤ 0 := by linarith
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hX
  have hanti : AntitoneOn g (Set.Icc a b) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b) hgcont hgderiv hgnonpos
  intro t ht
  have hgt : g t ≤ g a := hanti (Set.left_mem_Icc.mpr (ht.1.trans ht.2)) ht ht.1
  have hga : g a = 0 := by
    have h1 : x a - y a ≤ 0 := by linarith
    have h2 : (max (x a - y a) 0) ^ 2 = 0 := by simp [max_eq_right h1]
    simp [hgdef, h2]
  rw [hga] at hgt
  have h1 : Real.exp (c * t) * (max (x t - y t) 0) ^ 2 ≤ 0 := by simpa [hgdef] using hgt
  have hX : (max (x t - y t) 0) ^ 2 ≤ 0 := by
    have h := le_of_mul_le_mul_left
      (show Real.exp (c * t) * (max (x t - y t) 0) ^ 2 ≤ Real.exp (c * t) * 0 by simpa using h1)
      (Real.exp_pos _)
    simpa using h
  have h3 : (max (x t - y t) 0) ^ 2 = 0 := by nlinarith [sq_nonneg (max (x t - y t) 0)]
  have h4 : max (x t - y t) 0 = 0 := by
    have h6 : 0 ≤ max (x t - y t) 0 := le_max_right _ _
    nlinarith [h3]
  have h5 : x t - y t ≤ 0 := by
    have := le_max_left (x t - y t) 0
    rw [h4] at this
    linarith
  linarith

/-! ### The comparison principle for delay equations (scalar case) -/

/-- **The comparison principle for delay equations (scalar case).**  Let `F : DelayField ℝ` be a
delay field, `τ > 0` the delay, and let `x, y : ℝ → ℝ` be two solutions of the delay equation
`ẋ(t) = F.f ( t, x(t), x(t - τ) )` resp. `ẏ(t) = F.f ( t, y(t), y(t - τ) )` on `[0, T]`.  Assume

* the field is **monotone**: `F.f t u v ≤ F.f t u' v'` whenever `u ≤ u'` and `v ≤ v'`;
* the **histories are ordered**: `x r ≤ y r` for every `r ≤ 0`.

Then `x r ≤ y r` for every `r ∈ [0, T]`.

This is the classical comparison principle for delay differential equations (Hale, *Ordinary
Differential Equations*, Ch. 5).  The proof is the method of steps: on the step `[n τ, (n+1) τ]`
the delayed parts `x(· - τ)` and `y(· - τ)` are already ordered, so `x` is a *subsolution* of the
ordinary differential equation `u' = F.f ( t, u, y(t - τ) )` and `y` is a solution of it; the
one-step lemma `delay_comparison_step` applies.

Note that only the **monotonicity in the delayed state** is used (to obtain the subsolution
inequality); the monotonicity in the current state is not needed for the comparison, the Lipschitz
constant `F.K₂` in the current state playing the role of the "one-sided Lipschitz" bound. -/
theorem delay_comparison_subsolution {F : DelayField ℝ} {τ T : ℝ} (hτ : 0 < τ) (hT : 0 ≤ T)
    {x y : ℝ → ℝ} {fx : ℝ → ℝ}
    (hmono : ∀ t u u' v v', u ≤ u' → v ≤ v' → F.f t u v ≤ F.f t u' v')
    (hx : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt x (fx t) (Set.Icc 0 T) t)
    (hsub : ∀ t ∈ Set.Icc 0 T, fx t ≤ F.f t (x t) (x (t - τ)))
    (hy : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt y (F.f t (y t) (y (t - τ))) (Set.Icc 0 T) t)
    (horder : ∀ r ≤ 0, x r ≤ y r) :
    ∀ r ∈ Set.Icc 0 T, x r ≤ y r := by
  have hstep : ∀ n : ℕ, ((n + 1 : ℕ) : ℝ) * τ = (n : ℝ) * τ + τ := by
    intro n
    push_cast
    ring
  have hnext : ∀ n : ℕ, (n : ℝ) * τ ≤ ((n + 1 : ℕ) : ℝ) * τ := by
    intro n
    rw [hstep n]
    linarith
  -- the induction over the steps
  have hall : ∀ n : ℕ, ∀ r ∈ Set.Icc 0 (min T ((n : ℝ) * τ)), x r ≤ y r := by
    intro n
    induction n with
    | zero =>
        intro r hr
        have hr0 : r = 0 := by
          have h1 : min T (((0 : ℕ) : ℝ) * τ) = 0 := by
            rw [Nat.cast_zero, zero_mul]
            exact min_eq_right (by simpa using hT)
          rw [h1] at hr
          exact le_antisymm hr.2 (by linarith [hr.1])
        subst hr0
        exact horder 0 le_rfl
    | succ n ih =>
        intro r hr
        by_cases haT : T ≤ (n : ℝ) * τ
        · -- the induction hypothesis already covers `[0, T]`
          have hmin : min T ((n : ℝ) * τ) = T := min_eq_left haT
          have hbmin : min T (((n + 1 : ℕ) : ℝ) * τ) = T := by
            refine min_eq_left ?_
            calc T ≤ (n : ℝ) * τ := haT
              _ ≤ ((n + 1 : ℕ) : ℝ) * τ := hnext n
          have h1 := ih r
          rw [hmin] at h1
          rw [hbmin] at hr
          exact h1 hr
        · -- one more step
          have haT' : (n : ℝ) * τ < T := by linarith
          have hmin : min T ((n : ℝ) * τ) = (n : ℝ) * τ := min_eq_right (le_of_lt haT')
          have hbT : min T (((n + 1 : ℕ) : ℝ) * τ) ≤ T := min_le_left _ _
          have h0n : 0 ≤ (n : ℝ) * τ := mul_nonneg (Nat.cast_nonneg n) hτ.le
          -- the delayed parts are ordered on the step
          have hdel : ∀ t ∈ Set.Icc ((n : ℝ) * τ) (min T (((n + 1 : ℕ) : ℝ) * τ)),
              x (t - τ) ≤ y (t - τ) := by
            intro t ht
            have h1 : t - τ ≤ (n : ℝ) * τ := by
              have h2 : min T (((n + 1 : ℕ) : ℝ) * τ) ≤ ((n + 1 : ℕ) : ℝ) * τ := min_le_right _ _
              rw [hstep n] at h2
              have h3 : t ≤ (n : ℝ) * τ + τ := by
                have h4 := ht.2
                rw [hstep n] at h4
                linarith [h2]
              linarith
            by_cases h0 : t - τ ≤ 0
            · exact horder (t - τ) h0
            · have hmem : t - τ ∈ Set.Icc 0 (min T ((n : ℝ) * τ)) :=
                ⟨by have h5 : 0 < t - τ := lt_of_not_ge h0; linarith,
                  by rw [hmin]; linarith [h1]⟩
              exact ih (t - τ) hmem
          -- the derivatives on the step
          have hxs : ∀ t ∈ Set.Icc ((n : ℝ) * τ) (min T (((n + 1 : ℕ) : ℝ) * τ)),
              HasDerivWithinAt x (fx t)
                (Set.Icc ((n : ℝ) * τ) (min T (((n + 1 : ℕ) : ℝ) * τ))) t := by
            intro t ht
            have htT : t ∈ Set.Icc 0 T :=
              ⟨by linarith [h0n, ht.1], by linarith [ht.2, hbT]⟩
            exact (hx t htT).mono (fun s hs => ⟨by linarith [h0n, hs.1], le_trans hs.2 hbT⟩)
          have hys : ∀ t ∈ Set.Icc ((n : ℝ) * τ) (min T (((n + 1 : ℕ) : ℝ) * τ)),
              HasDerivWithinAt y (F.f t (y t) (y (t - τ)))
                (Set.Icc ((n : ℝ) * τ) (min T (((n + 1 : ℕ) : ℝ) * τ))) t := by
            intro t ht
            have htT : t ∈ Set.Icc 0 T :=
              ⟨by linarith [h0n, ht.1], by linarith [ht.2, hbT]⟩
            exact (hy t htT).mono (fun s hs => ⟨by linarith [h0n, hs.1], le_trans hs.2 hbT⟩)
          -- the subsolution inequality on the step
          set h : ℝ → ℝ → ℝ := fun t u => F.f t u (y (t - τ)) with hhdef
          have hsub' : ∀ t ∈ Set.Icc ((n : ℝ) * τ) (min T (((n + 1 : ℕ) : ℝ) * τ)),
              fx t ≤ h t (x t) := by
            intro t ht
            have htT : t ∈ Set.Icc 0 T :=
              ⟨by linarith [h0n, ht.1], by linarith [ht.2, hbT]⟩
            refine (hsub t htT).trans ?_
            rw [hhdef]
            exact hmono t (x t) (x t) (x (t - τ)) (y (t - τ)) le_rfl (hdel t ht)
          have hlip : ∀ t, LipschitzWith F.K₂ (fun u => h t u) := by
            intro t
            exact F.lip₂ t (y (t - τ))
          have hmemA : (n : ℝ) * τ ∈ Set.Icc 0 (min T ((n : ℝ) * τ)) :=
            ⟨by positivity, by simp [hmin]⟩
          have hstep' : ∀ t ∈ Set.Icc ((n : ℝ) * τ) (min T (((n + 1 : ℕ) : ℝ) * τ)),
              x t ≤ y t := by
            intro t ht
            have h1 : x ((n : ℝ) * τ) ≤ y ((n : ℝ) * τ) := ih _ hmemA
            exact delay_comparison_step (a := (n : ℝ) * τ)
              (b := min T (((n + 1 : ℕ) : ℝ) * τ)) hlip (hxs) (hsub') (hys) h1 t ht
          -- combine
          by_cases hr' : r ≤ (n : ℝ) * τ
          · have hmem : r ∈ Set.Icc 0 (min T ((n : ℝ) * τ)) :=
              ⟨by linarith [hr.1], by rw [hmin]; exact hr'⟩
            exact ih r hmem
          · exact hstep' r ⟨by linarith [hr.1], by linarith [hr.2]⟩
  -- the last step reaches `T`
  have hN : min T (((Nat.ceil (T / τ) : ℕ) : ℝ) * τ) = T := by
    have h1 : T / τ ≤ (Nat.ceil (T / τ) : ℝ) := Nat.le_ceil _
    have h2 : T ≤ (Nat.ceil (T / τ) : ℝ) * τ := by
      calc T = T / τ * τ := by field_simp
        _ ≤ (Nat.ceil (T / τ) : ℝ) * τ := mul_le_mul_of_nonneg_right h1 hτ.le
    exact min_eq_left h2
  intro r hr
  have h1 := hall (Nat.ceil (T / τ)) r
  rw [hN] at h1
  exact h1 hr

/-- **The comparison principle for delay equations (scalar case).**  Let `F : DelayField ℝ` be a
delay field, `τ > 0` the delay, and let `x, y : ℝ → ℝ` be two solutions of the delay equation
`ẋ(t) = F.f ( t, x(t), x(t - τ) )` resp. `ẏ(t) = F.f ( t, y(t), y(t - τ) )` on `[0, T]`.  Assume

* the field is **monotone**: `F.f t u v ≤ F.f t u' v'` whenever `u ≤ u'` and `v ≤ v'`;
* the **histories are ordered**: `x r ≤ y r` for every `r ≤ 0`.

Then `x r ≤ y r` for every `r ∈ [0, T]`.

This is the classical comparison principle for delay differential equations (Hale, *Ordinary
Differential Equations*, Ch. 5).  The proof is the method of steps: on the step `[n τ, (n+1) τ]`
the delayed parts `x(· - τ)` and `y(· - τ)` are already ordered, so `x` is a *subsolution* of the
ordinary differential equation `u' = F.f ( t, u, y(t - τ) )` and `y` is a solution of it; the
one-step lemma `delay_comparison_step` applies.

Note that only the **monotonicity in the delayed state** is used (to obtain the subsolution
inequality); the monotonicity in the current state is not needed for the comparison, the Lipschitz
constant `F.K₂` in the current state playing the role of the "one-sided Lipschitz" bound. -/
theorem delay_comparison_scalar {F : DelayField ℝ} {τ T : ℝ} (hτ : 0 < τ) (hT : 0 ≤ T)
    {x y : ℝ → ℝ}
    (hmono : ∀ t u u' v v', u ≤ u' → v ≤ v' → F.f t u v ≤ F.f t u' v')
    (hx : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt x (F.f t (x t) (x (t - τ))) (Set.Icc 0 T) t)
    (hy : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt y (F.f t (y t) (y (t - τ))) (Set.Icc 0 T) t)
    (horder : ∀ r ≤ 0, x r ≤ y r) :
    ∀ r ∈ Set.Icc 0 T, x r ≤ y r :=
  delay_comparison_subsolution hτ hT hmono hx (fun _ _ => le_rfl) hy horder

/-! ### The comparison principle for the solutions of `DelayExistence` -/

/-- **The comparison principle for delay solutions (on a finite interval).**  Two solutions of the
delay equation with the same delay and with ordered histories are ordered. -/
theorem delay_comparison_on {F : DelayField ℝ} {τ T : ℝ} (hτ : 0 < τ) (hT : 0 ≤ T)
    {φ ψ : ℝ → ℝ} {s : DelaySolutionOn F τ φ T} {u : DelaySolutionOn F τ ψ T}
    (hmono : ∀ t a a' b b', a ≤ a' → b ≤ b' → F.f t a b ≤ F.f t a' b')
    (horder : ∀ r ≤ 0, s.x r ≤ u.x r) :
    ∀ r ∈ Set.Icc 0 T, s.x r ≤ u.x r := by
  intro r hr
  refine delay_comparison_scalar hτ hT hmono ?_ ?_ horder r hr
  · intro t ht
    exact s.deriv t ht
  · intro t ht
    exact u.deriv t ht

/-- **The comparison principle for delay solutions (on the half line).**  Let `X` and `Y` be two
solutions of the delay equation `ẋ(t) = F.f ( t, x(t), x(t - τ) )` on `[0, ∞)` with the same delay
`τ > 0`, and suppose that their histories are ordered (`X t ≤ Y t` for `t ≤ 0`).  Then
`X t ≤ Y t` for every `t ≥ 0`.

This is the classical statement of the comparison principle for delay differential equations; it is
*strictly stronger* than the uniqueness theorem `CRNT.Dynamics.delay_solution_unique`, which
requires the two histories to coincide. -/
theorem delay_comparison_global {F : DelayField ℝ} {τ : ℝ} (hτ : 0 < τ)
    {X Y : ℝ → ℝ}
    (hmono : ∀ t a a' b b', a ≤ a' → b ≤ b' → F.f t a b ≤ F.f t a' b')
    (hX : ∀ T : ℝ, 0 ≤ T → IsDelaySolutionOn F τ X T)
    (hY : ∀ T : ℝ, 0 ≤ T → IsDelaySolutionOn F τ Y T)
    (horder : ∀ t ≤ 0, X t ≤ Y t) :
    ∀ t ≥ 0, X t ≤ Y t := by
  intro t ht
  refine delay_comparison_scalar hτ ht hmono ?_ ?_ horder t ⟨ht, le_rfl⟩
  · intro s hs
    exact (hX t ht).2 s hs
  · intro s hs
    exact (hY t ht).2 s hs

/-! ### The comparison principle in terms of the difference of the two fields -/

/-- **The comparison principle in terms of the difference of the two right-hand sides.**  Let `x` and
`y` be two solutions of the delay equation with the same delay, and suppose that the *difference*
of the two right-hand sides is nonpositive:
`F.f t (x t) (x (t - τ)) ≤ F.f t (y t) (y (t - τ))`.
Then `x ≤ y` on `[0, T]` whenever the histories are ordered.

This is the "one-sided" form of the comparison principle: it does not require the field to be
monotone, only the two right-hand sides to be ordered *along the two trajectories*.  It is the
form in which the comparison principle is used for a *supersolution* of a delay equation. -/
theorem delay_comparison_difference {F : DelayField ℝ} {τ T : ℝ} (hT : 0 ≤ T)
    {x y : ℝ → ℝ}
    (hfield : ∀ t ∈ Set.Icc 0 T,
        F.f t (x t) (x (t - τ)) - F.f t (y t) (y (t - τ)) ≤ 0)
    (hx : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt x (F.f t (x t) (x (t - τ))) (Set.Icc 0 T) t)
    (hy : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt y (F.f t (y t) (y (t - τ))) (Set.Icc 0 T) t)
    (horder : ∀ r ≤ 0, x r ≤ y r) :
    ∀ r ∈ Set.Icc 0 T, x r ≤ y r := by
  have hd : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt (fun s => x s - y s)
      (F.f t (x t) (x (t - τ)) - F.f t (y t) (y (t - τ))) (Set.Icc 0 T) t := by
    intro t ht
    exact (hx t ht).sub (hy t ht)
  have hcont : ContinuousOn (fun s : ℝ => x s - y s) (Set.Icc 0 T) := by
    intro t ht
    exact (hd t ht).continuousWithinAt
  have hderiv : ∀ t ∈ interior (Set.Icc 0 T),
      HasDerivWithinAt (fun s : ℝ => x s - y s)
        (F.f t (x t) (x (t - τ)) - F.f t (y t) (y (t - τ))) (interior (Set.Icc 0 T)) t := by
    intro t ht
    exact (hd t (interior_subset ht)).mono interior_subset
  have hnonpos : ∀ t ∈ interior (Set.Icc 0 T),
      F.f t (x t) (x (t - τ)) - F.f t (y t) (y (t - τ)) ≤ 0 := by
    intro t ht
    exact hfield t (interior_subset ht)
  have hanti : AntitoneOn (fun s : ℝ => x s - y s) (Set.Icc 0 T) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 T) hcont hderiv hnonpos
  intro r hr
  have h0mem : 0 ∈ Set.Icc 0 T := ⟨le_refl 0, hT⟩
  have h1 := hanti h0mem hr hr.1
  have h2 : x 0 - y 0 ≤ 0 := by
    have := horder 0 le_rfl
    linarith
  linarith

/-! ### The order version of uniqueness -/

/-- **Uniqueness from the comparison principle.**  Two solutions of the delay equation with
*mutually ordered* histories coincide.

Together with `CRNT.Dynamics.delay_solution_unique` (which assumes that the two histories
*coincide*) this shows that the delay flow is *strictly* order preserving: the comparison
principle `delay_comparison_global` is stronger than uniqueness. -/
theorem delay_comparison_eq {F : DelayField ℝ} {τ : ℝ} (hτ : 0 < τ)
    {X Y : ℝ → ℝ}
    (hmono : ∀ t a a' b b', a ≤ a' → b ≤ b' → F.f t a b ≤ F.f t a' b')
    (hX : ∀ T : ℝ, 0 ≤ T → IsDelaySolutionOn F τ X T)
    (hY : ∀ T : ℝ, 0 ≤ T → IsDelaySolutionOn F τ Y T)
    (horder : ∀ t ≤ 0, X t ≤ Y t) (horder' : ∀ t ≤ 0, Y t ≤ X t) :
    ∀ t, X t = Y t := by
  intro t
  by_cases ht : t ≤ 0
  · exact le_antisymm (horder t ht) (horder' t ht)
  · exact le_antisymm
      (delay_comparison_global hτ hmono hX hY horder t (le_of_not_ge ht))
      (delay_comparison_global hτ hmono hY hX horder' t (le_of_not_ge ht))

/-! ### The quantitative form: the exponential growth of the difference -/

/-- The **linear growth delay field** `G.f t u v = c u + d v`, with `c, d ≥ 0`.  It is the right-hand
side of the linear delay equation `ẇ = c w(t) + d w(t - τ)`, and it is used below for the
exponential growth estimate of the difference of two delay solutions. -/
noncomputable def growthDelayField (c d : ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d) : DelayField ℝ where
  f := fun _ u v => c * u + d * v
  cont := by fun_prop
  K₂ := Real.toNNReal c
  lip₂ := by
    intro t y
    refine LipschitzWith.of_dist_le_mul ?_
    intro u u'
    have h1 : c * u + d * y - (c * u' + d * y) = c * (u - u') := by ring
    rw [dist_eq_norm, h1, Real.norm_eq_abs, abs_mul, abs_of_nonneg hc, dist_eq_norm,
      Real.norm_eq_abs]
    have h2 : (Real.toNNReal c : ℝ) = c := Real.coe_toNNReal c hc
    rw [h2]
  M := 0
  C := Real.toNNReal (c + d)
  growth := by
    intro t u v
    have h1 : ‖c * u + d * v‖ ≤ |c| * ‖u‖ + |d| * ‖v‖ := by
      calc ‖c * u + d * v‖ ≤ ‖c * u‖ + ‖d * v‖ := norm_add_le _ _
        _ ≤ |c| * ‖u‖ + |d| * ‖v‖ := by
          have h2 : ‖c * u‖ ≤ |c| * ‖u‖ := by
            have := norm_mul_le c u
            rwa [Real.norm_eq_abs] at this
          have h3 : ‖d * v‖ ≤ |d| * ‖v‖ := by
            have := norm_mul_le d v
            rwa [Real.norm_eq_abs] at this
          linarith
    have h2 : |c| = c := abs_of_nonneg hc
    have h3 : |d| = d := abs_of_nonneg hd
    rw [h2, h3] at h1
    have h4 : c * ‖u‖ + d * ‖v‖ ≤ (c + d) * (‖u‖ + ‖v‖) := by
      have h5 : 0 ≤ d * ‖u‖ := mul_nonneg hd (norm_nonneg u)
      have h6 : 0 ≤ c * ‖v‖ := mul_nonneg hc (norm_nonneg v)
      nlinarith [h5, h6]
    have h7 : (Real.toNNReal (c + d) : ℝ) = c + d := Real.coe_toNNReal _ (by linarith)
    rw [h7]
    simpa [Real.norm_eq_abs] using h1.trans h4

/-- **An admissible growth rate exists.**  For `c, d ≥ 0` and `τ > 0` there is `ε ≥ 0` with
`c + d * exp (-ε * τ) = ε`; this is the characteristic equation of the linear delay equation
`ẇ = c w(t) + d w(t - τ)`, and `ε` is the growth rate of its solutions.

For `c + d > 0` the rate is positive. -/
theorem growth_rate_exists {c d τ : ℝ} (hτ : 0 < τ) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    ∃ ε : ℝ, 0 ≤ ε ∧ c + d * Real.exp (-ε * τ) = ε := by
  have hcont : Continuous (fun e : ℝ => e - c - d * Real.exp (-e * τ)) := by
    have h1 : Continuous (fun e : ℝ => -e * τ) := by fun_prop
    have h2 : Continuous (fun e : ℝ => Real.exp (-e * τ)) := Real.continuous_exp.comp h1
    have h3 : Continuous (fun e : ℝ => d * Real.exp (-e * τ)) := continuous_const.mul h2
    exact (continuous_id.sub continuous_const).sub h3
  have hf0 : (0 : ℝ) - c - d * Real.exp (-(0 : ℝ) * τ) ≤ 0 := by
    simp only [neg_zero, zero_mul, Real.exp_zero, mul_one]
    linarith
  have hf1 : 0 ≤ (c + d + 1) - c - d * Real.exp (-(c + d + 1) * τ) := by
    have h1 : 0 < Real.exp (-(c + d + 1) * τ) := Real.exp_pos _
    have h2 : Real.exp (-(c + d + 1) * τ) ≤ 1 := by
      have h3 : -(c + d + 1) * τ ≤ 0 := by
        have h4 : 0 ≤ (c + d + 1) * τ := mul_nonneg (by linarith) hτ.le
        linarith
      exact Real.exp_le_one_iff.mpr h3
    have h3 : d * Real.exp (-(c + d + 1) * τ) ≤ d * 1 :=
      mul_le_mul_of_nonneg_left h2 hd
    linarith
  obtain ⟨e, he, heq⟩ : ∃ e ∈ Set.Icc (0 : ℝ) (c + d + 1),
      (fun e : ℝ => e - c - d * Real.exp (-e * τ)) e = 0 := by
    have himg := intermediate_value_Icc (by linarith) hcont.continuousOn ⟨hf0, hf1⟩
    have himg2 : ∃ e ∈ Set.Icc (0 : ℝ) (c + d + 1),
        (fun e : ℝ => e - c - d * Real.exp (-e * τ)) e = 0 := by
      exact himg
    obtain ⟨e, he, heq⟩ := himg2
    exact ⟨e, he, heq⟩
  refine ⟨e, he.1, ?_⟩
  linarith [heq]

/-- **The elementary estimate `2 |a b| ≤ a² + b²`.** -/
private theorem two_mul_abs_le {a b : ℝ} : 2 * |a| * |b| ≤ a ^ 2 + b ^ 2 := by
  have h1 : 0 ≤ (|a| - |b|) ^ 2 := sq_nonneg _
  nlinarith [sq_abs a, sq_abs b]

/-- **The difference of two delay solutions satisfies a linear delay inequality.**  Let `x` and `y`
be two solutions of the delay equation `ẋ(t) = F.f ( t, x(t), x(t - τ) )` with the same delay
`τ > 0`, and suppose that the right-hand side is Lipschitz in the *delayed* state with constant
`K₃` (the Lipschitz constant `F.K₂` in the current state is part of the data of `F`).  Then the
*squared* difference `v t = (y t - x t)²` is a **subsolution** of the linear delay equation
`v' = c v(t) + d v(t - τ)` with `c = 2 K₂ + K₃` and `d = K₃`:

`v' ≤ c v(t) + d v(t - τ)`.

This is the estimate behind the exponential growth bound `delay_difference_exp_le`. -/
theorem delay_difference_sq_sub {F : DelayField ℝ} {τ : ℝ}
    (K₃ : ℝ≥0)
    (hlip₃ : ∀ t u v v', |F.f t u v - F.f t u v'| ≤ (K₃ : ℝ) * |v - v'|)
    {x y : ℝ → ℝ} {T : ℝ}
    (hx : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt x (F.f t (x t) (x (t - τ))) (Set.Icc 0 T) t)
    (hy : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt y (F.f t (y t) (y (t - τ))) (Set.Icc 0 T) t)
    (c d : ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hcd : 2 * (F.K₂ : ℝ) + (K₃ : ℝ) ≤ c) (hde : (K₃ : ℝ) ≤ d) :
    ∀ t ∈ Set.Icc 0 T,
      HasDerivWithinAt (fun s => (y s - x s) ^ 2)
        (2 * (y t - x t) * (F.f t (y t) (y (t - τ)) - F.f t (x t) (x (t - τ))))
        (Set.Icc 0 T) t ∧
      2 * (y t - x t) * (F.f t (y t) (y (t - τ)) - F.f t (x t) (x (t - τ)))
        ≤ c * (y t - x t) ^ 2 + d * (y (t - τ) - x (t - τ)) ^ 2 := by
  -- the difference of the two trajectories
  have hz : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt (fun s => y s - x s)
      (F.f t (y t) (y (t - τ)) - F.f t (x t) (x (t - τ))) (Set.Icc 0 T) t := by
    intro t ht
    exact (hy t ht).sub (hx t ht)
  -- the bound on the derivative of the difference
  have hbound : ∀ t ∈ Set.Icc 0 T,
      |F.f t (y t) (y (t - τ)) - F.f t (x t) (x (t - τ))|
        ≤ (F.K₂ : ℝ) * |y t - x t| + (K₃ : ℝ) * |y (t - τ) - x (t - τ)| := by
    intro t ht
    have hsplit : F.f t (y t) (y (t - τ)) - F.f t (x t) (x (t - τ))
        = (F.f t (y t) (y (t - τ)) - F.f t (x t) (y (t - τ)))
          + (F.f t (x t) (y (t - τ)) - F.f t (x t) (x (t - τ))) := by ring
    have h1 := (F.lip₂ t (y (t - τ))).dist_le_mul (y t) (x t)
    have h1' : |F.f t (y t) (y (t - τ)) - F.f t (x t) (y (t - τ))|
        ≤ (F.K₂ : ℝ) * |y t - x t| := by
      have h2 : dist (F.f t (y t) (y (t - τ))) (F.f t (x t) (y (t - τ)))
          = |F.f t (y t) (y (t - τ)) - F.f t (x t) (y (t - τ))| := by
        rw [dist_eq_norm, Real.norm_eq_abs]
      have h3 : dist (y t) (x t) = |y t - x t| := by rw [dist_eq_norm, Real.norm_eq_abs]
      rw [h2, h3] at h1
      exact h1
    have h2' := hlip₃ t (x t) (y (t - τ)) (x (t - τ))
    rw [hsplit]
    calc |(F.f t (y t) (y (t - τ)) - F.f t (x t) (y (t - τ)))
          + (F.f t (x t) (y (t - τ)) - F.f t (x t) (x (t - τ)))|
        ≤ |F.f t (y t) (y (t - τ)) - F.f t (x t) (y (t - τ))|
          + |F.f t (x t) (y (t - τ)) - F.f t (x t) (x (t - τ))| := abs_add_le _ _
        _ ≤ (F.K₂ : ℝ) * |y t - x t| + (K₃ : ℝ) * |y (t - τ) - x (t - τ)| :=
          add_le_add h1' h2'
  intro t ht
  refine ⟨?_, ?_⟩
  · -- the derivative of the squared difference
    have h1 := (hz t ht).pow 2
    convert h1 using 1; ring
  · -- the delay inequality for the squared difference
    have h1 := hbound t ht
    have h2 : 2 * (y t - x t) * (F.f t (y t) (y (t - τ)) - F.f t (x t) (x (t - τ)))
        ≤ 2 * |y t - x t| * |F.f t (y t) (y (t - τ)) - F.f t (x t) (x (t - τ))| := by
      have h4 : F.f t (y t) (y (t - τ)) - F.f t (x t) (x (t - τ))
          ≤ |F.f t (y t) (y (t - τ)) - F.f t (x t) (x (t - τ))| := le_abs_self _
      have h5 : 0 ≤ |y t - x t| := abs_nonneg _
      have h3 : (y t - x t) * (F.f t (y t) (y (t - τ)) - F.f t (x t) (x (t - τ)))
          ≤ |y t - x t| * |F.f t (y t) (y (t - τ)) - F.f t (x t) (x (t - τ))| := by
        calc (y t - x t) * (F.f t (y t) (y (t - τ)) - F.f t (x t) (x (t - τ)))
            ≤ |(y t - x t) * (F.f t (y t) (y (t - τ)) - F.f t (x t) (x (t - τ)))| := le_abs_self _
          _ = |y t - x t| * |F.f t (y t) (y (t - τ)) - F.f t (x t) (x (t - τ))| := abs_mul _ _
      linarith
    have h3 : 2 * |y t - x t| * |y (t - τ) - x (t - τ)|
        ≤ (y t - x t) ^ 2 + (y (t - τ) - x (t - τ)) ^ 2 :=
      two_mul_abs_le
    calc 2 * (y t - x t) * (F.f t (y t) (y (t - τ)) - F.f t (x t) (x (t - τ)))
        ≤ 2 * |y t - x t| * |F.f t (y t) (y (t - τ)) - F.f t (x t) (x (t - τ))| := h2
      _ ≤ 2 * |y t - x t| * ((F.K₂ : ℝ) * |y t - x t| + (K₃ : ℝ) * |y (t - τ) - x (t - τ)|) :=
          mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 2 * |y t - x t|)
      _ = 2 * (F.K₂ : ℝ) * |y t - x t| ^ 2
          + 2 * (K₃ : ℝ) * |y t - x t| * |y (t - τ) - x (t - τ)| := by ring
      _ ≤ 2 * (F.K₂ : ℝ) * (y t - x t) ^ 2
          + (K₃ : ℝ) * ((y t - x t) ^ 2 + (y (t - τ) - x (t - τ)) ^ 2) := by
        have h7 : 2 * |y t - x t| * |y (t - τ) - x (t - τ)|
            ≤ (y t - x t) ^ 2 + (y (t - τ) - x (t - τ)) ^ 2 := by
          have h8 := two_mul_abs_le (a := y t - x t) (b := y (t - τ) - x (t - τ))
          nlinarith [h8, sq_abs (y t - x t), sq_abs (y (t - τ) - x (t - τ))]
        have h9 : 0 ≤ (K₃ : ℝ) := K₃.coe_nonneg
        nlinarith [mul_le_mul_of_nonneg_left h7 h9, sq_abs (y t - x t),
          sq_abs (y (t - τ) - x (t - τ))]
      _ ≤ c * (y t - x t) ^ 2 + d * (y (t - τ) - x (t - τ)) ^ 2 := by
        have h4 : 0 ≤ (y t - x t) ^ 2 := sq_nonneg _
        have h5 : 0 ≤ (y (t - τ) - x (t - τ)) ^ 2 := sq_nonneg _
        have h6 : 0 ≤ (y (t - τ) - x (t - τ)) ^ 2 := sq_nonneg _
        nlinarith [mul_le_mul_of_nonneg_left hcd h4, mul_le_mul_of_nonneg_left hde h6]

/-- **The exponential growth of the difference of two delay solutions.**  Let `x` and `y` be two
solutions of the delay equation `ẋ(t) = F.f ( t, x(t), x(t - τ) )` with the same delay `τ > 0`, and
suppose that the right-hand side is Lipschitz in the *delayed* state with constant `K₃` (in
addition to the Lipschitz constant `F.K₂` in the current state, which is part of the data of
`F`).  Then the difference of the two solutions grows at most exponentially, with the rate `ε`
the (nonnegative) solution of the characteristic equation
`2 K₂ + K₃ + K₃ e^{-ε τ} = ε`:

`(y t - x t)² ≤ M e^{ε (t + τ)}`   for `t ≥ 0`,

where `M` bounds the squared difference on the history.

This is the quantitative form of the comparison principle: it is obtained by applying
`delay_comparison_subsolution` to the squared difference (a *subsolution* of the linear delay
equation `ẇ = c w(t) + d w(t - τ)`, see `delay_difference_sq_sub`) and to the explicit solution
`M e^{ε (t + τ)}` of that equation. -/
theorem delay_difference_exp_le {F : DelayField ℝ} {τ : ℝ} (hτ : 0 < τ)
    (K₃ : ℝ≥0)
    (hlip₃ : ∀ t u v v', |F.f t u v - F.f t u v'| ≤ (K₃ : ℝ) * |v - v'|)
    {x y : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hx : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt x (F.f t (x t) (x (t - τ))) (Set.Icc 0 T) t)
    (hy : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt y (F.f t (y t) (y (t - τ))) (Set.Icc 0 T) t)
    {ε M : ℝ}
    (hcond : 2 * (F.K₂ : ℝ) + (K₃ : ℝ) + (K₃ : ℝ) * Real.exp (-ε * τ) = ε)
    (hM : ∀ r ≤ 0, (y r - x r) ^ 2 ≤ M * Real.exp (ε * (r + τ))) :
    ∀ t ∈ Set.Icc 0 T, (y t - x t) ^ 2 ≤ M * Real.exp (ε * (t + τ)) := by
  set c : ℝ := 2 * (F.K₂ : ℝ) + (K₃ : ℝ) with hcdef
  set d : ℝ := (K₃ : ℝ) with hddef
  have hc0 : 0 ≤ c := by rw [hcdef]; positivity
  have hd0 : 0 ≤ d := by rw [hddef]; exact K₃.coe_nonneg
  -- the squared difference is a subsolution of the linear delay equation
  have hsub := delay_difference_sq_sub K₃ hlip₃ hx hy c d hc0 hd0
    (by rw [hcdef]) (by rw [hddef])
  -- the explicit solution of the linear delay equation
  set u : ℝ → ℝ := fun t => M * Real.exp (ε * (t + τ)) with hudef
  have hexp : ∀ s : ℝ, HasDerivAt (fun r => M * Real.exp (ε * (r + τ)))
      (ε * M * Real.exp (ε * (s + τ))) s := by
    intro s
    have h1 := (Real.hasDerivAt_exp (ε * (s + τ))).comp_of_eq s
      ((hasDerivAt_id s).add_const τ |>.const_mul ε) rfl
    have h2 := h1.const_mul M
    convert h2 using 1
    · funext r
      rfl
    · ring
  have hu : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt u (ε * u t) (Set.Icc 0 T) t := by
    intro t ht
    have h1 := hexp t
    rw [hudef]
    convert h1.hasDerivWithinAt using 1; ring
  have hudel : ∀ t ∈ Set.Icc 0 T, u (t - τ) = u t * Real.exp (-ε * τ) := by
    intro t ht
    simp only [hudef]
    have h1 : ε * ((t - τ) + τ) = ε * t := by ring
    rw [h1]
    have h2 : Real.exp (ε * (t + τ)) * Real.exp (-ε * τ) = Real.exp (ε * t) := by
      calc Real.exp (ε * (t + τ)) * Real.exp (-ε * τ)
          = Real.exp (ε * (t + τ)) / Real.exp (ε * τ) := by
              rw [show -ε * τ = -(ε * τ) by ring, Real.exp_neg]
              ring
        _ = Real.exp ((ε * (t + τ)) - ε * τ) := (Real.exp_sub _ _).symm
        _ = Real.exp (ε * t) := by rw [show ε * (t + τ) - ε * τ = ε * t by ring]
    rw [← h2]
    ring
  set G : DelayField ℝ := growthDelayField c d hc0 hd0 with hGdef
  have hGf : ∀ t u v, G.f t u v = c * u + d * v := by
    intro t u v
    rw [hGdef]
    rfl
  have hGmono : ∀ t u u' v v', u ≤ u' → v ≤ v' → G.f t u v ≤ G.f t u' v' := by
    intro t u u' v v' hu hv
    rw [hGf, hGf]
    have h1 : c * u + d * v ≤ c * u' + d * v' := by
      have h2 : 0 ≤ c := hc0
      have h3 : 0 ≤ d := hd0
      nlinarith [mul_le_mul_of_nonneg_left hu h2, mul_le_mul_of_nonneg_left hv h3]
    exact h1
  have hu' : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt u (G.f t (u t) (u (t - τ))) (Set.Icc 0 T) t := by
    intro t ht
    have h1 := hu t ht
    have h2 : c * u t + d * (u t * Real.exp (-ε * τ)) = ε * u t := by
      have h3 : c + d * Real.exp (-ε * τ) = ε := by
        rw [hcdef, hddef] at hcond
        linarith
      calc c * u t + d * (u t * Real.exp (-ε * τ))
          = (c + d * Real.exp (-ε * τ)) * u t := by ring
        _ = ε * u t := by rw [h3]
    rw [hGf, hudel t ht, h2]
    exact h1
  -- apply the comparison principle to the squared difference
  have hord : ∀ r ≤ 0, (y r - x r) ^ 2 ≤ u r := by
    intro r hr
    rw [hudef]
    exact hM r hr
  have hcomp := delay_comparison_subsolution (F := G) hτ hT hGmono
    (fun t ht => (hsub t ht).1) (fun t ht => (hsub t ht).2) (fun t ht => hu' t ht) hord
  intro t ht
  exact hcomp t ht

/-! ### Axiom audit (informational) -/
#print axioms delay_comparison_step
#print axioms delay_comparison_scalar
#print axioms delay_comparison_on
#print axioms delay_comparison_global
#print axioms delay_comparison_difference
#print axioms delay_comparison_eq
#print axioms delay_comparison_subsolution
#print axioms growthDelayField
#print axioms growth_rate_exists
#print axioms delay_difference_sq_sub
#print axioms delay_difference_exp_le

end General

end Dynamics
end CRNT
