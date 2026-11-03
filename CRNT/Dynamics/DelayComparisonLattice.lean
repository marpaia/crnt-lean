import CRNT.Dynamics.DelayComparison
import CRNT.Dynamics.MonotoneComparison
import CRNT.Extensions.DelayMassAction
import CRNT.Kinetics.Concentration

/-!
# The comparison principle for delay equations in the componentwise order

This module proves the **classical comparison principle for delay differential equations in the
componentwise (lattice) order**: let `F` be a delay field, `τ > 0` a delay, and let
`x, y` be two solutions of the delay equation

`ẋ(t) = F.f ( t, x(t), x(t − τ) )`,   `τ > 0`,

on a half line, with the *same* delay and with *ordered* histories (`x t ≤ y t` for `t ≤ 0`,
componentwise).  If the field is **off-diagonally monotone** in the current state (the Kamke
condition) and **monotone** in the delayed state, then

`x t ≤ y t`   for every `t ≥ 0`.

Reference: J. K. Hale, *Ordinary Differential Equations*, Wiley 1980, Chapter 5 ("Comparison
theorems"); see also A. A. Halanay, *Differential Equations and Applications*, 1983, Chapter 3.
The proof is the classical **method of steps**: on the step `[n τ, (n+1) τ]` the delayed part of
the subsolution is already ordered, so the subsolution is a subsolution of an *ordinary*
differential equation with a frozen delayed part, and the one-step comparison principle applies.

## The two towers of the delay content of the repository

The delay content of the repository comes in two *disjoint* towers, and this module works in the
first one only:

* the **general Banach-space delay field** `CRNT.Dynamics.DelayField`, with the solutions
  `CRNT.Dynamics.DelaySolutionOn` and the predicate `CRNT.Dynamics.IsDelaySolutionOn`; this is
  the tower of `CRNT.Dynamics.DelayExistence` (existence and uniqueness by the method of steps),
  of `CRNT.Dynamics.DelayComparison` (the comparison principle in the *scalar* setting) and of
  `CRNT.Dynamics.DelayHalanay` (the Halanay inequality and the semistability of the linear
  delay equation);
* the **mass-action delay system** `CRNT.Network.IsDelaySolution` of
  `CRNT/Extensions/DelayMassAction.lean`, i.e. the systems
  `ẋ(t) = ∑_r κ_r ( x(t − τ_r)^{y_r} y'_r − x(t)^{y_r} y_r )` of
  Lipták–Hangos–Pituk–Szederkényi.

The two towers do not meet: the mass-action delay system is a *specific* vector field on
`ℝ^S`, not an element of the general `DelayField` structure (the general tower works with an
arbitrary Banach space and an arbitrary right-hand side), and the mass-action tower moreover has
*one delay per reaction*.  The comparison principle below is stated for the first tower; the
last section of the module records, in the second tower, the precise obstruction to transferring
the statement to it.

## The relation to the scalar module `CRNT/Dynamics/DelayComparison.lean`

The campaign module `CRNT.Dynamics.DelayComparison` proves the comparison principle in the
**scalar** setting (`E = ℝ`); its own report records the precise remaining obligation:

> "(i) T1 for a GENERAL ordered Banach space `E` is NOT proved.  The proof uses the positive part
> (max (x−y)0)² of the difference, which needs a lattice (componentwise) structure on `E`; a
> general Banach space has none ... The natural extension is `E = ℝ^S` with the componentwise
> order (the repository's ODE prototype there is `CRNT.Monotone.kamke_comparison`); the delay
> version of that statement (with the delayed part handled by the method of steps) is not written
> here — it is the precise remaining obligation."

**This module discharges that obligation.**  The state space is `E = ℝ^S` (i.e. the repository's
`Concentration S`) with the **componentwise order** `Pi.le`, exactly the order used by
`CRNT.Monotone.kamke_comparison`; the hypothesis class is the *same* one, namely the Kamke
condition of off-diagonal monotonicity, transported to a delay field
(`CRNT.Dynamics.DelayField.KamkeOn`).  The one-step lemma `kamke_comparison_step` is the
componentwise analogue of `CRNT.Monotone.kamke_comparison` (it is the ODE statement on an
arbitrary interval `[a, b]`, for a *subsolution* below a solution), and it is proved with the
same "positive part squared" trick as the scalar module, summed over the components.

## The content of this module

* `CRNT.Dynamics.DelayField.KamkeOn`, `CRNT.Dynamics.DelayField.MonotoneDelayed`,
  `CRNT.Dynamics.DelayField.ComparisonMonotone`: the hypothesis class of the comparison
  principle for a delay field;
* `kamke_comparison_step`: the one-step comparison lemma in the componentwise order (the
  componentwise analogue of `CRNT.Monotone.kamke_comparison`);
* `delay_comparison_step_lattice`: the one-step lemma for a delay equation (the delayed part is
  frozen at the solution's delayed part);
* `delay_comparison_subsolution_lattice`: **the comparison principle**, subsolution version;
* `delay_comparison_lattice`: **the comparison principle**, the classical statement (two
  solutions of the same delay equation with ordered histories are ordered);
* `delay_comparison_lattice_on`, `delay_comparison_lattice_global`: the same statement for the
  solutions of `CRNT.Dynamics.DelayExistence` (on a finite interval and on the half line);
* `delay_comparison_lattice_eq`: the *order* version of uniqueness (two solutions with mutually
  ordered histories coincide);
* `linearDelayFieldLattice`, `linearDelayFieldLattice_comparisonMonotone`: a concrete instance
  of the hypothesis class (the linear delay equation `ẋ = a x + b x(· − τ)` with `a, b ≥ 0`),
  which shows that the hypothesis is satisfiable and natural;
* `CRNT.Network.massActionDelayField`, `CRNT.Network.massActionDelayField_delayField`,
  `CRNT.Network.massActionKamkeOn`: the mass-action delay field written as a function of the
  current state and of the delayed states, its identification with the repository's
  `CRNT.Network.delayField`, and the mass-action analogue of the Kamke condition;
* `CRNT.Network.twoSpeciesDegradation_field`,
  `CRNT.Network.twoSpeciesDegradation_not_massActionKamkeOn`: the **obstruction** — the
  mass-action delay field of the network `A + B → ∅` is *not* off-diagonally monotone in the
  current state.

## What is *not* proved here

* **The comparison principle for the mass-action delay system** of
  `CRNT/Extensions/DelayMassAction.lean` is *not* proved here, and the hypothesis class of this
  module does not apply to it.  Two independent obstructions:
  * the mass-action delay field is **not globally Lipschitz** in the current state (the
    monomials `x(t)^{y_r}` have unbounded derivative as soon as a reaction has a source
    complex of degree `≥ 2`), so it is not an element of `CRNT.Dynamics.DelayField`, whose
    Lipschitz hypothesis is global in the current state;
  * the mass-action delay field is **not off-diagonally monotone in the current state**: its
    current-state part is `−∑_r κ_r u^{y_r} y_r`, which is *decreasing* in `u`, whereas the
    Kamke condition requires the field to be *increasing* along a coordinate whose value is
    unchanged.  This is formalised here for the two-species degradation network `A + B → ∅`
    (`CRNT.Network.twoSpeciesDegradation_not_massActionKamkeOn`): the mass-action delay systems
    are *competitive*, not cooperative, and the comparison principle of this module (a statement
    about *cooperative* fields) therefore does not transfer to them.  (The mass-action tower
    moreover has one delay per reaction, while `CRNT.Dynamics.DelayField` has a single delay.)
    A comparison principle for the mass-action delay systems would need a *different* argument —
    the difference of two mass-action delay solutions is a *competitive* delay equation, whose
    solution operator is not positive — and is not attempted here.
* The comparison principle in a **general ordered Banach space** (i.e. for a state space that is
  a lattice but not `ℝ^S`) is not proved here: the proof sums the squares of the positive parts
  over the components, which requires the finite product structure of `ℝ^S`.
* The **path-space (LaSalle) theory** of delay equations is not touched here.
-/
namespace CRNT

open Filter Topology Set
open scoped BigOperators NNReal

set_option maxHeartbeats 800000

namespace Dynamics

section Lattice

variable {S : Type} [Fintype S]

namespace DelayField

/-- **The Kamke condition for a delay field.**  The delay field
`F.f : ℝ → (S → ℝ) → (S → ℝ) → (S → ℝ)` is *off-diagonally monotone* in the current state: for
every time `t`, every delayed value `v`, and all `a ≤ b` with `a i = b i`, one has
`F.f t a v i ≤ F.f t b v i`.

This is the delay analogue of `CRNT.Monotone.KamkeOn`; the two extra parameters are the time `t`
and the delayed value `v`.  Unlike `CRNT.Monotone.KamkeOn` it is stated *globally*, because the
Lipschitz bound `CRNT.Dynamics.DelayField.lip₂` of a delay field is global in the current state
as well: the set `K` of `CRNT.Monotone.KamkeOn` serves only to localize the Lipschitz bound and
to guarantee the closure under the componentwise maximum, and neither is needed here. -/
def KamkeOn (F : DelayField (S → ℝ)) : Prop :=
  ∀ t v a b, a ≤ b → ∀ i, a i = b i → F.f t a v i ≤ F.f t b v i

/-- **Monotonicity of a delay field in the delayed state.**  For every time `t`, every current
value `u` and all `v ≤ v'`, one has `F.f t u v i ≤ F.f t u v' i`. -/
def MonotoneDelayed (F : DelayField (S → ℝ)) : Prop :=
  ∀ t u v v', v ≤ v' → ∀ i, F.f t u v i ≤ F.f t u v' i

/-- **The comparison hypothesis for a delay field.**  The field is off-diagonally monotone in the
current state (the Kamke condition) and monotone in the delayed state.

A field satisfying this hypothesis is a *cooperative* delay field: the comparison principle
`delay_comparison_lattice` holds for it. -/
def ComparisonMonotone (F : DelayField (S → ℝ)) : Prop := F.KamkeOn ∧ F.MonotoneDelayed

end DelayField

/-! ### The one-step comparison lemma in the componentwise order -/

/-- **The one-step comparison lemma in the componentwise order.**  Let
`f : ℝ → (S → ℝ) → (S → ℝ)` be Lipschitz with constant `L` in its second argument and let it
satisfy the Kamke condition (off-diagonal monotonicity).  If `x` is a *subsolution* of the
ordinary differential equation `u' = f (t, u)` on `[a, b]` and `y` a *solution* of it, and if
`x a ≤ y a`, then `x t ≤ y t` on `[a, b]`.

This is the componentwise (lattice) analogue of `CRNT.Dynamics.delay_comparison_step` (the
scalar one-step lemma) and of `CRNT.Monotone.kamke_comparison` (the comparison principle for
cooperative systems); it is the ingredient of the method of steps below.  The proof is the
classical one: the function `V t = ∑ᵢ (max (x t i - y t i) 0)²` satisfies the differential
inequality `V' ≤ 2 L |S| V` with `V a = 0`, hence `V ≡ 0`. -/
theorem kamke_comparison_step {a b : ℝ} {f : ℝ → (S → ℝ) → (S → ℝ)} {L : ℝ≥0}
    (hlip : ∀ t, LipschitzWith L (f t))
    (hkamke : ∀ t u u', u ≤ u' → ∀ i, u i = u' i → f t u i ≤ f t u' i)
    {x y : ℝ → (S → ℝ)} {fx : ℝ → (S → ℝ)}
    (hx : ∀ t ∈ Set.Icc a b, HasDerivWithinAt x (fx t) (Set.Icc a b) t)
    (hsub : ∀ t ∈ Set.Icc a b, fx t ≤ f t (x t))
    (hy : ∀ t ∈ Set.Icc a b, HasDerivWithinAt y (f t (y t)) (Set.Icc a b) t)
    (ha : x a ≤ y a) :
    ∀ t ∈ Set.Icc a b, x t ≤ y t := by
  set D := Set.Icc a b
  set C : ℝ := 2 * L * Fintype.card S
  let w : ℝ → S → ℝ := fun t i => max (x t i - y t i) 0
  let V : ℝ → ℝ := fun t => ∑ i, (w t i) ^ 2
  have hV0 : ∀ t, 0 ≤ V t := fun t => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hw_le : ∀ t i, w t i ≤ Real.sqrt (V t) := by
    intro t i
    rw [Real.le_sqrt (le_max_right _ _) (hV0 t)]
    exact Finset.single_le_sum (f := fun i => (w t i) ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i)
  -- the derivative of `V`
  have hVd : ∀ t ∈ D, HasDerivWithinAt V
      (∑ i, 2 * w t i * (fx t i - f t (y t) i)) D t := by
    intro t ht
    refine HasDerivWithinAt.fun_sum fun i _ => ?_
    have hxi := (hasDerivWithinAt_pi.mp (hx t ht)) i
    have hyi := (hasDerivWithinAt_pi.mp (hy t ht)) i
    exact (Monotone.hasDerivAt_posPart_sq (x t i - y t i)).comp_hasDerivWithinAt t (hxi.sub hyi)
  -- the differential inequality `V' ≤ C V`
  have hVineq : ∀ t ∈ D, (∑ i, 2 * w t i * (fx t i - f t (y t) i)) ≤ C * V t := by
    intro t ht
    set z := x t ⊔ y t
    have hzy : ‖z - y t‖ ≤ Real.sqrt (V t) := by
      refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i => ?_
      have this : (z - y t) i = w t i := by
        simp only [z, Pi.sub_apply, Pi.sup_apply, w]
        rcases le_total (x t i) (y t i) with h | h
        · rw [max_eq_right h, max_eq_right (by linarith)]; ring
        · rw [max_eq_left h, max_eq_left (by linarith)]
      rw [this, Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact hw_le t i
    have hfl : ‖f t z - f t (y t)‖ ≤ (L : ℝ) * Real.sqrt (V t) :=
      (hlip t).norm_sub_le z (y t) |>.trans (mul_le_mul_of_nonneg_left hzy L.2)
    have hterm : ∀ i, 2 * w t i * (fx t i - f t (y t) i)
        ≤ 2 * (L : ℝ) * Real.sqrt (V t) * Real.sqrt (V t) := by
      intro i
      by_cases hpos : 0 < x t i - y t i
      · have hwi : w t i = x t i - y t i := max_eq_left hpos.le
        have hxz : x t ≤ z := le_sup_left
        have hxi : x t i = z i := by
          simp only [z, Pi.sup_apply]
          exact (max_eq_left (by linarith)).symm
        have h1 : f t (x t) i ≤ f t z i := hkamke t (x t) z hxz i hxi
        have h2 : f t z i - f t (y t) i ≤ (L : ℝ) * Real.sqrt (V t) := by
          have := norm_le_pi_norm (f t z - f t (y t)) i
          rw [Pi.sub_apply, Real.norm_eq_abs] at this
          linarith [le_abs_self (f t z i - f t (y t) i)]
        have hw0 : 0 ≤ w t i := le_max_right _ _
        calc 2 * w t i * (fx t i - f t (y t) i)
            ≤ 2 * w t i * (f t (x t) i - f t (y t) i) :=
              mul_le_mul_of_nonneg_left (by linarith [hsub t ht i]) (by positivity)
          _ ≤ 2 * w t i * ((L : ℝ) * Real.sqrt (V t)) :=
              mul_le_mul_of_nonneg_left (by linarith) (by positivity)
          _ ≤ 2 * Real.sqrt (V t) * ((L : ℝ) * Real.sqrt (V t)) := by
              have := hw_le t i
              have : 0 ≤ (L : ℝ) * Real.sqrt (V t) := by positivity
              nlinarith
          _ = 2 * (L : ℝ) * Real.sqrt (V t) * Real.sqrt (V t) := by ring
      · have hwi : w t i = 0 := max_eq_right (not_lt.mp hpos)
        rw [hwi, mul_zero, zero_mul]
        positivity
    calc (∑ i, 2 * w t i * (fx t i - f t (y t) i))
        ≤ ∑ _i : S, 2 * (L : ℝ) * Real.sqrt (V t) * Real.sqrt (V t) :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = C * V t := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc (2 * (L : ℝ)),
            Real.mul_self_sqrt (hV0 t)]
          simp only [C]; ring
  -- the auxiliary function `g t = exp (-C t) * V t` is nonincreasing
  let g : ℝ → ℝ := fun t => Real.exp (-C * t) * V t
  have hgd : ∀ t ∈ D, HasDerivWithinAt g
      (Real.exp (-C * t) * (-C) * V t +
        Real.exp (-C * t) * ∑ i, 2 * w t i * (fx t i - f t (y t) i)) D t := by
    intro t ht
    have he : HasDerivWithinAt (fun t => Real.exp (-C * t)) (Real.exp (-C * t) * (-C)) D t := by
      have := ((hasDerivAt_id t).const_mul (-C)).exp
      simpa using this.hasDerivWithinAt
    exact he.mul (hVd t ht)
  have hanti : AntitoneOn g D := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b)
      (fun t ht => (hgd t ht).continuousWithinAt)
      (fun t ht => (hgd t (interior_subset ht)).mono interior_subset) ?_
    intro t ht
    have := hVineq t (interior_subset ht)
    have hep := Real.exp_pos (-C * t)
    nlinarith [mul_le_mul_of_nonneg_left this hep.le]
  have hV00 : V a = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    have : x a i - y a i ≤ 0 := by linarith [ha i]
    simp [w, max_eq_right this]
  intro t ht
  have h0D : a ∈ D := ⟨le_refl a, ht.1.trans ht.2⟩
  have hgt : g t ≤ g a := hanti h0D ht ht.1
  simp only [g, mul_zero, hV00] at hgt
  have hVt : V t = 0 := by
    have := Real.exp_pos (-C * t)
    have : V t ≤ 0 := by nlinarith [hV0 t]
    linarith [hV0 t]
  intro i
  have hwi : w t i ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (w t j))).mp hVt i (Finset.mem_univ i)
  have : max (x t i - y t i) 0 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hwi
  have := le_max_left (x t i - y t i) 0
  linarith

/-! ### The one-step comparison lemma for delay equations -/

/-- **The one-step comparison lemma for delay equations (componentwise order).**  Let
`F : DelayField (S → ℝ)` be a delay field, `τ` the delay and `[a, b]` a step.  Let `x` be a
*subsolution* of the delay equation `ẋ(t) = F.f ( t, x(t), x(t - τ) )` and `y` a *solution* of it
on the step, and suppose that the delayed parts are ordered on the step
(`x (t - τ) ≤ y (t - τ)`) and that `x a ≤ y a`.  If the field is off-diagonally monotone in the
current state (`CRNT.Dynamics.DelayField.KamkeOn`) and monotone in the delayed state
(`CRNT.Dynamics.DelayField.MonotoneDelayed`), then `x t ≤ y t` on the step.

The proof: on the step the delayed part of `y` is known, so `x` is a subsolution of the ordinary
differential equation `u' = F.f ( t, u, y (t - τ) )` and `y` a solution of it; the one-step lemma
`kamke_comparison_step` applies. -/
theorem delay_comparison_step_lattice {F : DelayField (S → ℝ)} {τ a b : ℝ}
    (hkamke : F.KamkeOn) (hdel : F.MonotoneDelayed)
    {x y : ℝ → (S → ℝ)} {fx : ℝ → (S → ℝ)}
    (hx : ∀ t ∈ Set.Icc a b, HasDerivWithinAt x (fx t) (Set.Icc a b) t)
    (hsub : ∀ t ∈ Set.Icc a b, fx t ≤ F.f t (x t) (x (t - τ)))
    (hy : ∀ t ∈ Set.Icc a b, HasDerivWithinAt y (F.f t (y t) (y (t - τ))) (Set.Icc a b) t)
    (hdelayed : ∀ t ∈ Set.Icc a b, x (t - τ) ≤ y (t - τ))
    (ha : x a ≤ y a) :
    ∀ t ∈ Set.Icc a b, x t ≤ y t := by
  -- the effective ordinary differential equation on the step
  set g : ℝ → (S → ℝ) → (S → ℝ) := fun t u => F.f t u (y (t - τ)) with hgdef
  have hlip : ∀ t, LipschitzWith F.K₂ (g t) := by
    intro t
    exact F.lip₂ t (y (t - τ))
  have hkamke' : ∀ t u u', u ≤ u' → ∀ i, u i = u' i → g t u i ≤ g t u' i := by
    intro t u u' hle i heq
    exact hkamke t (y (t - τ)) u u' hle i heq
  -- the subsolution inequality for the effective equation
  have hsub' : ∀ t ∈ Set.Icc a b, fx t ≤ g t (x t) := by
    intro t ht
    have h1 := hdel t (x t) (x (t - τ)) (y (t - τ)) (hdelayed t ht)
    exact (hsub t ht).trans h1
  -- `y` solves the effective equation
  have hy' : ∀ t ∈ Set.Icc a b, HasDerivWithinAt y (g t (y t)) (Set.Icc a b) t := by
    intro t ht
    exact hy t ht
  exact kamke_comparison_step (a := a) (b := b) (f := g) (L := F.K₂) hlip hkamke'
    hx hsub' hy' ha

/-! ### The comparison principle for delay equations in the componentwise order -/

/-- **The comparison principle for delay equations in the componentwise order (subsolution
version).**  Let `F : DelayField (S → ℝ)` be a delay field, `τ > 0` the delay, and let
`x, y : ℝ → (S → ℝ)` be such that

* `x` is a *subsolution* of the delay equation `ẋ(t) = F.f ( t, x(t), x(t - τ) )` on `[0, T]`
  (i.e. `x' t ≤ F.f t (x t) (x (t - τ))`),
* `y` is a *solution* of it on `[0, T]`,
* the **histories are ordered**: `x r ≤ y r` for every `r ≤ 0`.

Assume that the field is off-diagonally monotone in the current state
(`CRNT.Dynamics.DelayField.KamkeOn`) and monotone in the delayed state
(`CRNT.Dynamics.DelayField.MonotoneDelayed`).  Then `x r ≤ y r` for every `r ∈ [0, T]`.

This is the classical comparison principle for delay differential equations (Hale, *Ordinary
Differential Equations*, Ch. 5) in the componentwise order; the proof is the method of steps, as
in the scalar module `CRNT.Dynamics.DelayComparison`. -/
theorem delay_comparison_subsolution_lattice {F : DelayField (S → ℝ)} {τ T : ℝ} (hτ : 0 < τ)
    (hT : 0 ≤ T) {x y : ℝ → (S → ℝ)} {fx : ℝ → (S → ℝ)}
    (hkamke : F.KamkeOn) (hdel : F.MonotoneDelayed)
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
          have hdel' : ∀ t ∈ Set.Icc ((n : ℝ) * τ) (min T (((n + 1 : ℕ) : ℝ) * τ)),
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
          have hsub' : ∀ t ∈ Set.Icc ((n : ℝ) * τ) (min T (((n + 1 : ℕ) : ℝ) * τ)),
              fx t ≤ F.f t (x t) (x (t - τ)) := by
            intro t ht
            have htT : t ∈ Set.Icc 0 T :=
              ⟨by linarith [h0n, ht.1], by linarith [ht.2, hbT]⟩
            exact hsub t htT
          have hmemA : (n : ℝ) * τ ∈ Set.Icc 0 (min T ((n : ℝ) * τ)) :=
            ⟨by positivity, by simp [hmin]⟩
          -- the one-step comparison
          have hstep' : ∀ t ∈ Set.Icc ((n : ℝ) * τ) (min T (((n + 1 : ℕ) : ℝ) * τ)),
              x t ≤ y t := by
            intro t ht
            have h1 : x ((n : ℝ) * τ) ≤ y ((n : ℝ) * τ) := ih _ hmemA
            exact delay_comparison_step_lattice hkamke hdel hxs hsub' hys hdel' h1 t ht
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

/-- **The comparison principle for delay equations in the componentwise order.**  Let
`F : DelayField (S → ℝ)` be a delay field, `τ > 0` the delay, and let `x, y : ℝ → (S → ℝ)` be two
solutions of the delay equation `ẋ(t) = F.f ( t, x(t), x(t - τ) )` on `[0, T]`.  Assume

* the field is **off-diagonally monotone in the current state** and **monotone in the delayed
  state** (`CRNT.Dynamics.DelayField.ComparisonMonotone`);
* the **histories are ordered**: `x r ≤ y r` for every `r ≤ 0`.

Then `x r ≤ y r` for every `r ∈ [0, T]`.

This is the classical comparison principle for delay differential equations (Hale, *Ordinary
Differential Equations*, Ch. 5) in the componentwise order; it is the exact analogue of
`CRNT.Monotone.kamke_comparison` for delay equations, and the vector-valued counterpart of
`CRNT.Dynamics.delay_comparison_scalar`. -/
theorem delay_comparison_lattice {F : DelayField (S → ℝ)} {τ T : ℝ} (hτ : 0 < τ) (hT : 0 ≤ T)
    {x y : ℝ → (S → ℝ)}
    (hk : F.ComparisonMonotone)
    (hx : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt x (F.f t (x t) (x (t - τ))) (Set.Icc 0 T) t)
    (hy : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt y (F.f t (y t) (y (t - τ))) (Set.Icc 0 T) t)
    (horder : ∀ r ≤ 0, x r ≤ y r) :
    ∀ r ∈ Set.Icc 0 T, x r ≤ y r := by
  exact delay_comparison_subsolution_lattice hτ hT hk.1 hk.2 hx (fun _ _ => le_rfl) hy horder

/-- **The comparison principle for delay solutions (on a finite interval), in the componentwise
order.**  Two solutions of the delay equation with the same delay and with ordered histories are
ordered. -/
theorem delay_comparison_lattice_on {F : DelayField (S → ℝ)} {τ T : ℝ} (hτ : 0 < τ) (hT : 0 ≤ T)
    {φ ψ : ℝ → (S → ℝ)} {s : DelaySolutionOn F τ φ T} {u : DelaySolutionOn F τ ψ T}
    (hk : F.ComparisonMonotone)
    (horder : ∀ r ≤ 0, s.x r ≤ u.x r) :
    ∀ r ∈ Set.Icc 0 T, s.x r ≤ u.x r := by
  intro r hr
  refine delay_comparison_lattice hτ hT hk ?_ ?_ horder r hr
  · intro t ht
    exact s.deriv t ht
  · intro t ht
    exact u.deriv t ht

/-- **The comparison principle for delay solutions on the half line, in the componentwise
order.**  Let `X` and `Y` be two solutions of the delay equation `ẋ(t) = F.f ( t, x(t), x(t - τ) )`
on `[0, ∞)` with the same delay `τ > 0`, and suppose that their histories are ordered
(`X t ≤ Y t` for `t ≤ 0`).  Then `X t ≤ Y t` for every `t ≥ 0`.

This is the classical statement of the comparison principle for delay differential equations; it
is *strictly stronger* than the uniqueness theorem `CRNT.Dynamics.delay_solution_unique`, which
requires the two histories to coincide. -/
theorem delay_comparison_lattice_global {F : DelayField (S → ℝ)} {τ : ℝ} (hτ : 0 < τ)
    {X Y : ℝ → (S → ℝ)}
    (hk : F.ComparisonMonotone)
    (hX : ∀ T : ℝ, 0 ≤ T → IsDelaySolutionOn F τ X T)
    (hY : ∀ T : ℝ, 0 ≤ T → IsDelaySolutionOn F τ Y T)
    (horder : ∀ t ≤ 0, X t ≤ Y t) :
    ∀ t ≥ 0, X t ≤ Y t := by
  intro t ht
  refine delay_comparison_lattice hτ ht hk ?_ ?_ horder t ⟨ht, le_rfl⟩
  · intro s hs
    exact (hX t ht).2 s hs
  · intro s hs
    exact (hY t ht).2 s hs

/-- **Uniqueness of the delay solution in the componentwise order.**  Two solutions of the delay
equation with *mutually ordered* histories coincide.

Together with `CRNT.Dynamics.delay_solution_unique` (which assumes that the two histories
*coincide*) this shows that the delay flow is *strictly* order preserving: the comparison
principle `delay_comparison_lattice_global` is stronger than uniqueness. -/
theorem delay_comparison_lattice_eq {F : DelayField (S → ℝ)} {τ : ℝ} (hτ : 0 < τ)
    {X Y : ℝ → (S → ℝ)}
    (hk : F.ComparisonMonotone)
    (hX : ∀ T : ℝ, 0 ≤ T → IsDelaySolutionOn F τ X T)
    (hY : ∀ T : ℝ, 0 ≤ T → IsDelaySolutionOn F τ Y T)
    (horder : ∀ t ≤ 0, X t ≤ Y t) (horder' : ∀ t ≤ 0, Y t ≤ X t) :
    ∀ t, X t = Y t := by
  intro t
  by_cases ht : t ≤ 0
  · exact le_antisymm (horder t ht) (horder' t ht)
  · exact le_antisymm
      (delay_comparison_lattice_global hτ hk hX hY horder t (le_of_not_ge ht))
      (delay_comparison_lattice_global hτ hk hY hX horder' t (le_of_not_ge ht))

/-! ### A concrete instance of the hypothesis class -/

/-- **The linear delay field** `F.f t u v = a u + b v` on `S → ℝ`, with `a, b ≥ 0`.  It is the
right-hand side of the linear delay equation `ẋ(t) = a x(t) + b x(t - τ)`. -/
noncomputable def linearDelayFieldLattice (a b : ℝ) : DelayField (S → ℝ) where
  f := fun _ u v => (a : ℝ) • u + (b : ℝ) • v
  cont := by
    fun_prop
  K₂ := Real.toNNReal |a|
  lip₂ := by
    intro t y
    refine LipschitzWith.of_dist_le_mul ?_
    intro u u'
    have h1 : (a : ℝ) • u + (b : ℝ) • y - ((a : ℝ) • u' + (b : ℝ) • y) = (a : ℝ) • (u - u') := by
      simp only [smul_sub]; abel
    rw [dist_eq_norm, dist_eq_norm, h1, norm_smul, Real.norm_eq_abs]
    have h2 : (Real.toNNReal |a| : ℝ) = |a| := Real.coe_toNNReal _ (abs_nonneg _)
    rw [h2]
  M := 0
  C := Real.toNNReal (|a| + |b|)
  growth := by
    intro t x y
    have h1 : ‖(a : ℝ) • x + (b : ℝ) • y‖ ≤ |a| * ‖x‖ + |b| * ‖y‖ := by
      calc ‖(a : ℝ) • x + (b : ℝ) • y‖ ≤ ‖(a : ℝ) • x‖ + ‖(b : ℝ) • y‖ := norm_add_le _ _
        _ ≤ |a| * ‖x‖ + |b| * ‖y‖ := by
          have h2 : ‖(a : ℝ) • x‖ = |a| * ‖x‖ := by rw [norm_smul, Real.norm_eq_abs]
          have h3 : ‖(b : ℝ) • y‖ = |b| * ‖y‖ := by rw [norm_smul, Real.norm_eq_abs]
          rw [h2, h3]
    have h4 : |a| * ‖x‖ + |b| * ‖y‖ ≤ (|a| + |b|) * (‖x‖ + ‖y‖) := by
      have h5 : 0 ≤ |b| * ‖x‖ := mul_nonneg (abs_nonneg _) (norm_nonneg _)
      have h6 : 0 ≤ |a| * ‖y‖ := mul_nonneg (abs_nonneg _) (norm_nonneg _)
      nlinarith [h5, h6]
    have h7 : (Real.toNNReal (|a| + |b|) : ℝ) = |a| + |b| := Real.coe_toNNReal _ (by positivity)
    rw [h7]
    exact le_trans h1 (by simpa using h4)

/-- **The linear delay field satisfies the comparison hypothesis.**  The linear delay equation
`ẋ(t) = a x(t) + b x(t - τ)` with `a, b ≥ 0` is cooperative, so the comparison principle
`delay_comparison_lattice` applies to it: two of its solutions with ordered histories are
ordered. -/
theorem linearDelayFieldLattice_comparisonMonotone (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (linearDelayFieldLattice (S := S) a b).ComparisonMonotone := by
  have hf : ∀ (t : ℝ) (u v : S → ℝ) (i : S),
      (linearDelayFieldLattice (S := S) a b).f t u v i = a * u i + b * v i := by
    intro t u v i
    simp only [linearDelayFieldLattice, Pi.add_apply, Pi.smul_apply]
    rw [smul_eq_mul, smul_eq_mul]
  constructor
  · intro t v u u' hle i heq
    have h1 : a * u i + b * v i ≤ a * u' i + b * v i := by
      have h2 := mul_le_mul_of_nonneg_left (hle i) ha
      linarith
    rw [hf, hf]
    exact h1
  · intro t u v v' hle i
    have h1 : a * u i + b * v i ≤ a * u i + b * v' i := by
      have h2 := mul_le_mul_of_nonneg_left (hle i) hb
      linarith
    rw [hf, hf]
    exact h1

end Lattice

end Dynamics

/-! ### The mass-action delay tower: the comparison hypothesis is not satisfied -/

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **The right-hand side of the mass-action delay equation, as a function of the current state
`u` and of the delayed states `v r`.**  This is the two-argument version of
`CRNT.Network.delayField`: the delayed state of the reaction `r` is the state of the system at
the time `t - τ r`.  It is the object on which the Kamke condition of the first tower,
`CRNT.Dynamics.DelayField.KamkeOn`, would have to be checked. -/
noncomputable def massActionDelayField (N : Network S) (κ : N.RateConstants)
    (u : Concentration S) (v : N.R → Concentration S) : Concentration S :=
  fun s => ∑ r, κ.k r * ((N.reaction r).source.massActionMonomial (v r) *
      ((N.reaction r).target s : ℝ) -
    (N.reaction r).source.massActionMonomial u * ((N.reaction r).source s : ℝ))

/-- **The bridge to the repository's delay field.**  The right-hand side of the mass-action delay
equation along a trajectory `x` is the two-argument field evaluated at the current state and at
the delayed states. -/
theorem massActionDelayField_delayField (N : Network S) (κ : N.RateConstants) (τ : N.R → ℝ)
    (x : ℝ → Concentration S) (t : ℝ) :
    N.delayField κ τ x t = N.massActionDelayField κ (x t) (fun r => x (t - τ r)) := by
  funext s
  rfl

/-- **The Kamke condition for the mass-action delay field.**  The mass-action delay field is
off-diagonally monotone in the current state: for all `u ≤ u'` with `u i = u' i`, the field at
species `i` does not decrease.  This is the mass-action analogue of
`CRNT.Dynamics.DelayField.KamkeOn`. -/
def massActionKamkeOn (N : Network S) (κ : N.RateConstants) : Prop :=
  ∀ (u u' : Concentration S) (v : N.R → Concentration S),
    u ≤ u' → ∀ i, u i = u' i → ∀ s,
      N.massActionDelayField κ u v s ≤ N.massActionDelayField κ u' v s

/-- **The two-species degradation network** `A + B → ∅`: a single reaction consuming one unit of
each of the two species. -/
def twoSpeciesDegradation : Network (Fin 2) where
  R := Unit
  decEqR := inferInstance
  fintypeR := inferInstance
  reaction := fun _ => ⟨fun _ => 1, Complex.zero⟩

/-- The rate constants of the two-species degradation network (every rate is `1`). -/
def twoSpeciesDegradationRates : RateConstants twoSpeciesDegradation where
  k := fun _ => 1
  positive := fun _ => by norm_num

/-- **The mass-action delay field of the two-species degradation network.**  At the first species
the field is `−u_A u_B`, independently of the delayed states (the reaction has no product). -/
theorem twoSpeciesDegradation_field (u : Concentration (Fin 2))
    (v : twoSpeciesDegradation.R → Concentration (Fin 2)) :
    twoSpeciesDegradation.massActionDelayField twoSpeciesDegradationRates u v 0
      = -(u 0 * u 1) := by
  simp only [massActionDelayField]
  refine (Finset.sum_eq_single () (by intro b _ hne; exact absurd (Subsingleton.elim b ()) hne)
    (by intro h; exact absurd (Finset.mem_univ _) h)).trans ?_
  simp [twoSpeciesDegradation, twoSpeciesDegradationRates, Complex.massActionMonomial,
    Fin.prod_univ_two]

/-- **The mass-action delay field is not off-diagonally monotone in the current state.**  For the
two-species degradation network `A + B → ∅` the mass-action delay field at the first species is
`−u_A u_B`, which *decreases* when the second concentration increases; the Kamke condition of
`CRNT.Dynamics.DelayField.KamkeOn` would require it to increase.

This is the precise obstruction that prevents the comparison principle of this module from
applying to the mass-action delay systems: the mass-action delay systems are *competitive* in
the current state, not cooperative, and the comparison principle of this module is a statement
about *cooperative* fields. -/
theorem twoSpeciesDegradation_not_massActionKamkeOn :
    ¬ massActionKamkeOn twoSpeciesDegradation twoSpeciesDegradationRates := by
  intro h
  -- the two states: `u = (1, 1)` and `u' = (1, 2)`
  set u : Concentration (Fin 2) := fun _ => 1 with hu
  set u' : Concentration (Fin 2) := fun i => (i.val + 1 : ℝ) with hu'
  set v : twoSpeciesDegradation.R → Concentration (Fin 2) :=
    fun _ => (0 : Concentration (Fin 2)) with hv
  have hle : u ≤ u' := by
    intro i
    have h1 : (0 : ℝ) ≤ (i.val : ℝ) := Nat.cast_nonneg i.val
    simp only [hu, hu']
    linarith
  have heq : u 0 = u' 0 := by
    simp [hu, hu']
  have h1 := h u u' v hle 0 heq 0
  rw [twoSpeciesDegradation_field, twoSpeciesDegradation_field] at h1
  simp [hu, hu'] at h1
  linarith

end Network

/-! ### Axiom audit (informational) -/

#print axioms CRNT.Dynamics.DelayField.KamkeOn
#print axioms CRNT.Dynamics.DelayField.MonotoneDelayed
#print axioms CRNT.Dynamics.DelayField.ComparisonMonotone
#print axioms CRNT.Dynamics.kamke_comparison_step
#print axioms CRNT.Dynamics.delay_comparison_step_lattice
#print axioms CRNT.Dynamics.delay_comparison_subsolution_lattice
#print axioms CRNT.Dynamics.delay_comparison_lattice
#print axioms CRNT.Dynamics.delay_comparison_lattice_on
#print axioms CRNT.Dynamics.delay_comparison_lattice_global
#print axioms CRNT.Dynamics.delay_comparison_lattice_eq
#print axioms CRNT.Dynamics.linearDelayFieldLattice
#print axioms CRNT.Dynamics.linearDelayFieldLattice_comparisonMonotone
#print axioms CRNT.Network.massActionDelayField_delayField
#print axioms CRNT.Network.twoSpeciesDegradation_field
#print axioms CRNT.Network.twoSpeciesDegradation_not_massActionKamkeOn

end CRNT
