import CRNT.Extensions.DelayLyapunov
import CRNT.Equilibria.DetailedBalanced
import CRNT.Theorems.DeficiencyZero.Dissipation
import CRNT.Theorems.DeficiencyZero.Lyapunov
import CRNT.Examples.ReversiblePair
import CRNT.Dynamics.MassActionField
import Mathlib.Topology.ClusterPt
import Mathlib.Topology.Compactness.Compact

/-!
# Semistability of delay mass-action systems

This module completes the *semistability* layer of field-map leaf E3 (delay systems) that
`CRNT/Extensions/DelayLyapunov.lean` left open.  Recall the setting: a delay mass-action system

`ẋ(t) = ∑_r κ_r ( x(t − τ_r)^{y_r} y'_r − x(t)^{y_r} y_r )`

has the Lipták–Hangos–Pituk–Szederkényi Lyapunov–Krasovskii functional

`V(t) = ∑_s (x_s(t)(log x_s(t) − log x*_s) − 1 + x*_s) + ∑_r κ_r ∫_{t−τ_r}^{t} g_r(u) du`,

with `g_r(u) = x(u)^{y_r}(L_{y_r}(u) − 1) + x*^{y_r}` and `L_c(u) = ∑_s c_s (log u_s − log x*_s)`.
`CRNT.Extensions.DelayLyapunov` proves that `V` is nonincreasing along every positive solution
whenever `x*` is complex balanced.  The present module adds the *strict* part (the entropy
production of the delayed system) and the *LaSalle* part (the convergence to an equilibrium).

## The strict decrease

The derivative of `V` is the entropy production of the delayed system,

`V'(t) = ∑_r κ_r ( A_r(t−τ_r) ( L_{y'_r}(t) − L_{y_r}(t−τ_r) + 1 ) − A_r(t) )`,

`A_r(s) = x(s)^{y_r}`.  Two facts drive everything.

1. **The termwise Gibbs bound.**  With `a = A_r(t−τ_r)` and `b = x*^{y_r} exp(L_{y'_r}(t))`,
   the scalar inequality `a (log b − log a + 1) ≤ b` gives

   `A_r(t−τ_r)( L_{y'_r}(t) − L_{y_r}(t−τ_r) + 1 ) ≤ b`,

   with equality **iff** `a = b`, i.e. iff the *monomial ratio* `ρ_c(s) = x(s)^c / x*^c` of the
   source complex at the delayed time equals the monomial ratio of the target complex at the
   current time.

2. **The complex-balance identity.**  `∑_r κ_r x*^{y_r} ( e^{L_{y'_r}(t)} − e^{L_{y_r}(t)} ) = 0`,
   because `x*` is complex balanced (this is `Network.sum_kineticMap_mul` paired with the
   monomial vector of `x*`).  Consequently the sum of the bounds above is exactly `0`.

Hence `V'(t) < 0` as soon as **one** reaction violates the ratio condition
(`delayLyapunov_deriv_neg_of_mismatch`), and `V'(t) = 0` exactly when the ratio condition holds
for *every* reaction (`delayLyapunov_deriv_eq_zero_iff`).

The zero set of `V'` is described by the *ratio condition*

`ρ_{y_r}(t−τ_r) = ρ_{y'_r}(t)`,

which is **not** the same as "`x(t)` is a steady state" once the delays are non-trivial: the
delayed value enters the condition.  Two consequences are proved.

* `delayLyapunov_deriv_neg_of_not_steady`: if the solution segment at time `t` is *ratio
  consistent* (the delayed ratios agree with the current ones — automatic when `τ ≡ 0`), then
  the vanishing of `V'` forces the ratio condition, hence complex balance at `x(t)`
  (`complexBalanced_of_ratio_const`), hence `x(t)` is a steady state.  Contrapositively, a
  non-steady `x(t)` makes `V'` strictly negative.  The consistency hypothesis is the exact
  content of the statement "the delayed values do not change the ratios"; without it the zero
  set of `V'` is the ratio-consistency set, not the set of steady states.
* `delayLyapunov_deriv_neg_of_not_steady_noDelay`: the same statement with no delay at all,
  where the functional is the Horn–Jackson entropy of the *instantaneous* mass-action field.

The classical statement for the instantaneous field is recorded separately in
`delayEntropy_dissipation_neg_of_not_steady`: the logarithmic dissipation
`⟨log(x/x*), f(x)⟩` is strictly negative at every concentration that is not a steady state.

## The LaSalle part

* `delayLyapunov_nonneg`: the functional is nonnegative (hence bounded below) for nonnegative
  delays;
* `delayLyapunov_tendsto`: along a positive solution `V(t)` converges to a limit;
* `delay_limit_isSteadyState`: **every limit of a delay solution is a mass-action steady state
  of the instantaneous field** — the key structural fact behind the LaSalle argument: the
  displacement over a window of length one tends to `0`, while the (continuous) delay field at
  the limit is the *instantaneous* mass-action field at the limit;
* `delay_semistability`: with a relatively compact range and a singleton ω-limit set (the set
  of accumulation points of the range at infinity), the solution converges to that point, and the
  point is a mass-action steady state: the delay system is *semistable*.

## What is *not* proved here

* **Existence theory** for delay mass-action systems (well-posedness on the segment space
  `C([−τ_max, 0], ℝ^S)`) is *not* provided: no semiflow is constructed, so the ω-limit set
  used here is the set of *cluster points at infinity of the given trajectory*, not the ω-limit
  set of a delay semiflow.
* **The full LaSalle invariance principle** for the delay semiflow (invariance of the ω-limit
  set inside the segment space) is not formalised; the conclusion is obtained from the
  structural fact `delay_limit_isSteadyState`.  In particular the ω-limit set in the
  *concentration* space is not enough to conclude semistability: a cluster point `y` of the
  trajectory need not be an equilibrium, because the *delayed* values may accumulate at a
  different point.  `delay_semistability` therefore carries the explicit hypothesis that the
  ω-limit set is a singleton; the general statement needs the segment space.
* **Uniqueness** of the limiting equilibrium is not available: without deficiency-zero
  uniqueness in the delayed compatibility class one cannot rule out a continuum of steady
  states in the ω-limit set.

## A concrete instance

`CRNT.Examples.ReversiblePair` (the canonical deficiency-zero network `A ⇌ B`) is used as a
delay network: the delay is an extra parameter `τ : R → ℝ` attached to the channels.  The
concentration `(k₁, k₀)` is detailed balanced (`equilibrium_detailedBalanced`), hence a steady
state and a constant solution of the delayed system (`equilibrium_isDelaySolution`); at the
positive non-equilibrium `(2, 2)` (`offEquilibrium_notSteadyState`) the derivative of the
functional is strictly negative, with and without delay
(`delayLyapunovDeriv_neg_at_offEquilibrium`, `delayLyapunovDeriv_neg_at_offEquilibrium_delayed`).

Depends on: `CRNT.Extensions.DelayLyapunov`, `CRNT.Equilibria.DetailedBalanced`,
`CRNT.Theorems.DeficiencyZero.Dissipation`, `CRNT.Theorems.DeficiencyZero.Lyapunov`,
`CRNT.Examples.ReversiblePair`.
-/

namespace CRNT

namespace Network

open scoped BigOperators
open Filter Topology Set

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ### Monomial ratios -/

/-- **The monomial ratio.**  The ratio of the mass-action monomial of the complex `c` at the
concentration `z` to its value at the positive reference concentration `xs`:
`ρ_c(z) = x(z)^c / x*^c`.  For a detailed-balanced network these ratios are the quantities whose
constancy across a reaction encodes (reactionwise) detailed balance. -/
noncomputable def delayRatio (xs : Concentration S) (c : Complex S) (z : Concentration S) : ℝ :=
  c.massActionMonomial z / c.massActionMonomial xs

omit [DecidableEq S] in
/-- The monomial ratio is positive at positive concentrations. -/
theorem delayRatio_pos {xs : Concentration S} (hxs : xs.Positive) {c : Complex S}
    {z : Concentration S} (hz : z.Positive) : 0 < delayRatio xs c z :=
  div_pos (Complex.massActionMonomial_pos hz _) (Complex.massActionMonomial_pos hxs _)

omit [DecidableEq S] in
/-- The exponential of the logarithmic ratio is the monomial ratio. -/
theorem exp_delayLogRatio_eq_delayRatio {xs : Concentration S} (hxs : xs.Positive) (c : Complex S)
    {z : Concentration S} (hz : z.Positive) :
    Real.exp (delayLogRatio xs c z) = delayRatio xs c z := by
  have h := massActionMonomial_eq_mul_exp_logRatio hxs hz c
  unfold delayRatio
  rw [h]
  exact (eq_div_iff (Complex.massActionMonomial_pos hxs _).ne').mpr (by ring)

omit [DecidableEq S] in
/-- Two monomial ratios agree iff the cross-multiplied monomials agree. -/
theorem delayRatio_eq_iff {xs : Concentration S} {c d : Complex S} {z w : Concentration S}
    (hc : 0 < c.massActionMonomial xs) (hd : 0 < d.massActionMonomial xs) :
    delayRatio xs c z = delayRatio xs d w ↔
      c.massActionMonomial z * d.massActionMonomial xs
        = d.massActionMonomial w * c.massActionMonomial xs := by
  unfold delayRatio
  exact div_eq_div_iff hc.ne' hd.ne'

omit [DecidableEq S] in
/-- The logarithm of the monomial ratio is the logarithmic ratio. -/
theorem log_delayRatio_eq_delayLogRatio {xs : Concentration S} (hxs : xs.Positive) (c : Complex S)
    {z : Concentration S} (hz : z.Positive) :
    Real.log (delayRatio xs c z) = delayLogRatio xs c z := by
  rw [← exp_delayLogRatio_eq_delayRatio hxs c hz, Real.log_exp]

/-! ### The scalar Gibbs inequality and its equality case -/

/-- The Gibbs inequality `a (log b − log a + 1) ≤ b` is an equality exactly when `a = b`. -/
theorem mul_log_sub_log_add_one_eq_iff {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    a * (Real.log b - Real.log a + 1) = b ↔ a = b := by
  constructor
  · intro h
    have h' : a * (Real.log b - Real.log a) = b - a := by linarith
    exact eq_of_mul_log_sub_eq ha hb h'
  · intro h
    subst h
    ring

/-! ### The derivative of the Lyapunov–Krasovskii functional -/

/-- **The derivative of the Lyapunov–Krasovskii functional.**  This is the entropy production of
the delayed system at time `t`. -/
noncomputable def delayLyapunovDeriv (N : Network S) (κ : N.RateConstants) (τ : N.R → ℝ)
    {xs : Concentration S} (x : ℝ → Concentration S) (t : ℝ) : ℝ :=
  ∑ r, κ.k r * ((N.reaction r).source.massActionMonomial (x (t - τ r)) *
      (delayLogRatio xs (N.reaction r).target (x t) -
        delayLogRatio xs (N.reaction r).source (x (t - τ r)) + 1) -
    (N.reaction r).source.massActionMonomial (x t))

/-- The derivative of the functional is `delayLyapunovDeriv`. -/
theorem delayLyapunov_deriv (N : Network S) (κ : N.RateConstants) (τ : N.R → ℝ)
    {xs : Concentration S} {x : ℝ → Concentration S}
    (hx : N.IsDelaySolution κ τ x) (hpos : ∀ t, (x t).Positive) (t : ℝ) :
    HasDerivAt (N.delayLyapunov κ τ xs x) (N.delayLyapunovDeriv κ τ (xs := xs) x t) t :=
  N.delayLyapunov_hasDerivAt κ τ hx hpos t

/-- **The termwise Gibbs bound for the delayed derivative.**  For a single reaction `r`, the
contribution to `V'(t)` is bounded by the "instantaneous" term
`x*^{y_r} (e^{L_{y'_r}(t)} − e^{L_{y_r}(t)})`. -/
theorem delayLyapunov_deriv_term_le (N : Network S) (κ : N.RateConstants) (τ : N.R → ℝ)
    {xs : Concentration S} (hxs : xs.Positive) {x : ℝ → Concentration S}
    (hpos : ∀ t, (x t).Positive) (t : ℝ) (r : N.R) :
    κ.k r * ((N.reaction r).source.massActionMonomial (x (t - τ r)) *
        (delayLogRatio xs (N.reaction r).target (x t) -
          delayLogRatio xs (N.reaction r).source (x (t - τ r)) + 1) -
        (N.reaction r).source.massActionMonomial (x t))
      ≤ κ.k r * ((N.reaction r).source.massActionMonomial xs) *
        (Real.exp (delayLogRatio xs (N.reaction r).target (x t)) -
          Real.exp (delayLogRatio xs (N.reaction r).source (x t))) := by
  have hms0 : 0 < (N.reaction r).source.massActionMonomial xs :=
    Complex.massActionMonomial_pos hxs _
  have hA0 : 0 < (N.reaction r).source.massActionMonomial (x (t - τ r)) :=
    Complex.massActionMonomial_pos (hpos _) _
  have hAe : (N.reaction r).source.massActionMonomial (x (t - τ r)) =
      (N.reaction r).source.massActionMonomial xs *
        Real.exp (delayLogRatio xs (N.reaction r).source (x (t - τ r))) :=
    massActionMonomial_eq_mul_exp_logRatio hxs (hpos _) _
  have hB0 : 0 < (N.reaction r).source.massActionMonomial xs *
      Real.exp (delayLogRatio xs (N.reaction r).target (x t)) :=
    mul_pos hms0 (Real.exp_pos _)
  have hlogA : Real.log ((N.reaction r).source.massActionMonomial (x (t - τ r))) =
      Real.log ((N.reaction r).source.massActionMonomial xs) +
        delayLogRatio xs (N.reaction r).source (x (t - τ r)) := by
    rw [hAe, Real.log_mul hms0.ne' (Real.exp_pos _).ne', Real.log_exp]
  have hlogB : Real.log ((N.reaction r).source.massActionMonomial xs *
      Real.exp (delayLogRatio xs (N.reaction r).target (x t))) =
      Real.log ((N.reaction r).source.massActionMonomial xs) +
        delayLogRatio xs (N.reaction r).target (x t) := by
    rw [Real.log_mul hms0.ne' (Real.exp_pos _).ne', Real.log_exp]
  have key := mul_log_sub_log_add_one_le hA0 hB0
  rw [hlogA, hlogB] at key
  have hmt : (N.reaction r).source.massActionMonomial (x t) =
      (N.reaction r).source.massActionMonomial xs *
        Real.exp (delayLogRatio xs (N.reaction r).source (x t)) :=
    massActionMonomial_eq_mul_exp_logRatio hxs (hpos _) _
  rw [hmt]
  have hk := (κ.positive r).le
  have : (N.reaction r).source.massActionMonomial (x (t - τ r)) *
        (delayLogRatio xs (N.reaction r).target (x t) -
          delayLogRatio xs (N.reaction r).source (x (t - τ r)) + 1) ≤
      (N.reaction r).source.massActionMonomial xs *
        Real.exp (delayLogRatio xs (N.reaction r).target (x t)) := by linarith
  nlinarith

/-- **The equality case of the termwise bound.**  The bound of
`delayLyapunov_deriv_term_le` is an equality iff the monomial ratio of the source complex at the
delayed time equals the monomial ratio of the target complex at the current time. -/
theorem delayLyapunov_deriv_term_eq_iff (N : Network S) (τ : N.R → ℝ)
    {xs : Concentration S} (hxs : xs.Positive) {x : ℝ → Concentration S}
    (hpos : ∀ t, (x t).Positive) (t : ℝ) (r : N.R) :
    (N.reaction r).source.massActionMonomial (x (t - τ r)) *
        (delayLogRatio xs (N.reaction r).target (x t) -
          delayLogRatio xs (N.reaction r).source (x (t - τ r)) + 1)
      = (N.reaction r).source.massActionMonomial xs *
        Real.exp (delayLogRatio xs (N.reaction r).target (x t))
      ↔ delayRatio xs (N.reaction r).source (x (t - τ r))
        = delayRatio xs (N.reaction r).target (x t) := by
  have hms0 : 0 < (N.reaction r).source.massActionMonomial xs :=
    Complex.massActionMonomial_pos hxs _
  have hmst0 : 0 < (N.reaction r).target.massActionMonomial xs :=
    Complex.massActionMonomial_pos hxs _
  have hA0 : 0 < (N.reaction r).source.massActionMonomial (x (t - τ r)) :=
    Complex.massActionMonomial_pos (hpos _) _
  have hB0 : 0 < (N.reaction r).source.massActionMonomial xs *
      Real.exp (delayLogRatio xs (N.reaction r).target (x t)) :=
    mul_pos hms0 (Real.exp_pos _)
  have hAe : (N.reaction r).source.massActionMonomial (x (t - τ r)) =
      (N.reaction r).source.massActionMonomial xs *
        Real.exp (delayLogRatio xs (N.reaction r).source (x (t - τ r))) :=
    massActionMonomial_eq_mul_exp_logRatio hxs (hpos _) _
  have hlogA : Real.log ((N.reaction r).source.massActionMonomial (x (t - τ r))) =
      Real.log ((N.reaction r).source.massActionMonomial xs) +
        delayLogRatio xs (N.reaction r).source (x (t - τ r)) := by
    rw [hAe, Real.log_mul hms0.ne' (Real.exp_pos _).ne', Real.log_exp]
  have hlogB : Real.log ((N.reaction r).source.massActionMonomial xs *
      Real.exp (delayLogRatio xs (N.reaction r).target (x t))) =
      Real.log ((N.reaction r).source.massActionMonomial xs) +
        delayLogRatio xs (N.reaction r).target (x t) := by
    rw [Real.log_mul hms0.ne' (Real.exp_pos _).ne', Real.log_exp]
  have hexp : Real.exp (delayLogRatio xs (N.reaction r).target (x t)) =
      (N.reaction r).target.massActionMonomial (x t) /
        (N.reaction r).target.massActionMonomial xs :=
    exp_delayLogRatio_eq_delayRatio hxs (N.reaction r).target (hpos t)
  constructor
  · intro h
    -- the Gibbs inequality is an equality, hence `A = B`
    have hlogform : (N.reaction r).source.massActionMonomial (x (t - τ r)) *
          (Real.log ((N.reaction r).source.massActionMonomial xs *
                Real.exp (delayLogRatio xs (N.reaction r).target (x t))) -
            Real.log ((N.reaction r).source.massActionMonomial (x (t - τ r))) + 1) =
          (N.reaction r).source.massActionMonomial xs *
            Real.exp (delayLogRatio xs (N.reaction r).target (x t)) := by
      rw [hlogA, hlogB]
      linarith
    have hAB : (N.reaction r).source.massActionMonomial (x (t - τ r)) =
        (N.reaction r).source.massActionMonomial xs *
          Real.exp (delayLogRatio xs (N.reaction r).target (x t)) :=
      (mul_log_sub_log_add_one_eq_iff hA0 hB0).mp hlogform
    -- `A = B` is exactly the ratio condition
    have hr : (N.reaction r).source.massActionMonomial (x (t - τ r)) /
          (N.reaction r).source.massActionMonomial xs =
        (N.reaction r).target.massActionMonomial (x t) /
          (N.reaction r).target.massActionMonomial xs := by
      calc (N.reaction r).source.massActionMonomial (x (t - τ r)) /
            (N.reaction r).source.massActionMonomial xs
          = ((N.reaction r).source.massActionMonomial xs *
              Real.exp (delayLogRatio xs (N.reaction r).target (x t))) /
            (N.reaction r).source.massActionMonomial xs := by rw [hAB]
        _ = Real.exp (delayLogRatio xs (N.reaction r).target (x t)) := by
          field_simp
        _ = (N.reaction r).target.massActionMonomial (x t) /
            (N.reaction r).target.massActionMonomial xs := hexp
    exact hr
  · intro hr
    -- the ratio condition gives `A = B`, hence the equality of the bounds
    have hAB : (N.reaction r).source.massActionMonomial (x (t - τ r)) =
        (N.reaction r).source.massActionMonomial xs *
          Real.exp (delayLogRatio xs (N.reaction r).target (x t)) := by
      have hcross := (delayRatio_eq_iff hms0 hmst0).mp hr
      have h3 : (N.reaction r).source.massActionMonomial (x (t - τ r)) =
          ((N.reaction r).source.massActionMonomial xs *
            (N.reaction r).target.massActionMonomial (x t)) /
            (N.reaction r).target.massActionMonomial xs :=
        (eq_div_iff hmst0.ne').mpr (by rw [hcross]; ring)
      rw [h3, hexp]
      ring
    have hlogform : (N.reaction r).source.massActionMonomial (x (t - τ r)) *
          (Real.log ((N.reaction r).source.massActionMonomial xs *
                Real.exp (delayLogRatio xs (N.reaction r).target (x t))) -
            Real.log ((N.reaction r).source.massActionMonomial (x (t - τ r))) + 1) =
          (N.reaction r).source.massActionMonomial xs *
            Real.exp (delayLogRatio xs (N.reaction r).target (x t)) :=
      (mul_log_sub_log_add_one_eq_iff hA0 hB0).mpr hAB
    rw [hlogA, hlogB] at hlogform
    linarith

/-- **The equality of a term with its bound.**  The contribution of reaction `r` to the
derivative of the Lyapunov–Krasovskii functional equals its bound exactly when the monomial ratio
of the source complex at the delayed time agrees with the monomial ratio of the target complex at
the current time. -/
theorem delayLyapunov_deriv_term_eq_bound_iff (N : Network S) (κ : N.RateConstants) (τ : N.R → ℝ)
    {xs : Concentration S} (hxs : xs.Positive) {x : ℝ → Concentration S}
    (hpos : ∀ t, (x t).Positive) (t : ℝ) (r : N.R) :
    (κ.k r * ((N.reaction r).source.massActionMonomial (x (t - τ r)) *
        (delayLogRatio xs (N.reaction r).target (x t) -
          delayLogRatio xs (N.reaction r).source (x (t - τ r)) + 1) -
        (N.reaction r).source.massActionMonomial (x t))) =
      κ.k r * ((N.reaction r).source.massActionMonomial xs) *
        (Real.exp (delayLogRatio xs (N.reaction r).target (x t)) -
          Real.exp (delayLogRatio xs (N.reaction r).source (x t)))
    ↔ delayRatio xs (N.reaction r).source (x (t - τ r))
      = delayRatio xs (N.reaction r).target (x t) := by
  have hk : 0 < κ.k r := κ.positive r
  have hmt : (N.reaction r).source.massActionMonomial (x t) =
      (N.reaction r).source.massActionMonomial xs *
        Real.exp (delayLogRatio xs (N.reaction r).source (x t)) :=
    massActionMonomial_eq_mul_exp_logRatio hxs (hpos t) (N.reaction r).source
  constructor
  · intro h
    have h' : κ.k r *
          ((N.reaction r).source.massActionMonomial (x (t - τ r)) *
            (delayLogRatio xs (N.reaction r).target (x t) -
              delayLogRatio xs (N.reaction r).source (x (t - τ r)) + 1) -
            (N.reaction r).source.massActionMonomial (x t)) =
        κ.k r * ((N.reaction r).source.massActionMonomial xs *
          (Real.exp (delayLogRatio xs (N.reaction r).target (x t)) -
            Real.exp (delayLogRatio xs (N.reaction r).source (x t)))) := by
      have hre : κ.k r * ((N.reaction r).source.massActionMonomial xs *
          (Real.exp (delayLogRatio xs (N.reaction r).target (x t)) -
            Real.exp (delayLogRatio xs (N.reaction r).source (x t)))) =
        κ.k r * ((N.reaction r).source.massActionMonomial xs) *
          (Real.exp (delayLogRatio xs (N.reaction r).target (x t)) -
            Real.exp (delayLogRatio xs (N.reaction r).source (x t))) := by ring
      rw [hre]
      exact h
    have hcancel := (mul_left_cancel₀ hk.ne' h')
    rw [hmt] at hcancel
    have hinner : (N.reaction r).source.massActionMonomial (x (t - τ r)) *
          (delayLogRatio xs (N.reaction r).target (x t) -
            delayLogRatio xs (N.reaction r).source (x (t - τ r)) + 1) =
        (N.reaction r).source.massActionMonomial xs *
          Real.exp (delayLogRatio xs (N.reaction r).target (x t)) := by linarith
    exact (delayLyapunov_deriv_term_eq_iff N τ hxs hpos t r).mp hinner
  · intro hrat
    have hinner := (delayLyapunov_deriv_term_eq_iff N τ hxs hpos t r).mpr hrat
    have h' : (N.reaction r).source.massActionMonomial (x (t - τ r)) *
          (delayLogRatio xs (N.reaction r).target (x t) -
            delayLogRatio xs (N.reaction r).source (x (t - τ r)) + 1) -
          (N.reaction r).source.massActionMonomial (x t) =
        (N.reaction r).source.massActionMonomial xs *
          (Real.exp (delayLogRatio xs (N.reaction r).target (x t)) -
            Real.exp (delayLogRatio xs (N.reaction r).source (x t))) := by
      rw [hmt, hinner]
      ring
    have : κ.k r *
          ((N.reaction r).source.massActionMonomial (x (t - τ r)) *
            (delayLogRatio xs (N.reaction r).target (x t) -
              delayLogRatio xs (N.reaction r).source (x (t - τ r)) + 1) -
            (N.reaction r).source.massActionMonomial (x t)) =
        κ.k r * ((N.reaction r).source.massActionMonomial xs) *
          (Real.exp (delayLogRatio xs (N.reaction r).target (x t)) -
            Real.exp (delayLogRatio xs (N.reaction r).source (x t))) := by
      rw [h']
      ring
    exact this

/-! ### The strict decrease -/

/-- **The strict decrease of the delayed derivative.**  The derivative of the
Lyapunov–Krasovskii functional is strictly negative as soon as one reaction violates the ratio
condition, i.e. as soon as the monomial ratio of the source complex at the delayed time differs
from the monomial ratio of the target complex at the current time. -/
theorem delayLyapunov_deriv_neg_of_mismatch
    (N : Network S) (κ : N.RateConstants) (τ : N.R → ℝ) {xs : Concentration S}
    (hxs : xs.Positive) (hcb : N.IsComplexBalanced κ xs)
    {x : ℝ → Concentration S} (hpos : ∀ t, (x t).Positive) (t : ℝ)
    (hmis : ∃ r, delayRatio xs (N.reaction r).source (x (t - τ r))
        ≠ delayRatio xs (N.reaction r).target (x t)) :
    N.delayLyapunovDeriv κ τ (xs := xs) x t < 0 := by
  -- the sum of the bounds vanishes by complex balance at `xs`
  have hsumU : (∑ r, κ.k r * ((N.reaction r).source.massActionMonomial xs) *
      (Real.exp (delayLogRatio xs (N.reaction r).target (x t)) -
        Real.exp (delayLogRatio xs (N.reaction r).source (x t)))) = 0 := by
    have hker := (N.isComplexBalanced_iff_kineticMap κ xs).mp hcb
    have hpair := N.sum_kineticMap_mul κ (N.complexMonomialVector xs)
      (fun c => Real.exp (delayLogRatio xs c.val (x t)))
    rw [hker] at hpair
    simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero] at hpair
    rw [hpair]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp [sourceIdx, targetIdx]
  -- one reaction violates the ratio condition
  obtain ⟨r₀, hne⟩ := hmis
  have hlt0 : κ.k r₀ * ((N.reaction r₀).source.massActionMonomial (x (t - τ r₀)) *
        (delayLogRatio xs (N.reaction r₀).target (x t) -
          delayLogRatio xs (N.reaction r₀).source (x (t - τ r₀)) + 1) -
        (N.reaction r₀).source.massActionMonomial (x t))
      < κ.k r₀ * ((N.reaction r₀).source.massActionMonomial xs) *
        (Real.exp (delayLogRatio xs (N.reaction r₀).target (x t)) -
          Real.exp (delayLogRatio xs (N.reaction r₀).source (x t))) := by
    have hle := delayLyapunov_deriv_term_le N κ τ hxs hpos t r₀
    have hne' : (N.reaction r₀).source.massActionMonomial (x (t - τ r₀)) *
          (delayLogRatio xs (N.reaction r₀).target (x t) -
            delayLogRatio xs (N.reaction r₀).source (x (t - τ r₀)) + 1) ≠
        (N.reaction r₀).source.massActionMonomial xs *
          Real.exp (delayLogRatio xs (N.reaction r₀).target (x t)) :=
      fun h => hne ((delayLyapunov_deriv_term_eq_iff N τ hxs hpos t r₀).mp h)
    have hne'' : (κ.k r₀ *
          ((N.reaction r₀).source.massActionMonomial (x (t - τ r₀)) *
            (delayLogRatio xs (N.reaction r₀).target (x t) -
              delayLogRatio xs (N.reaction r₀).source (x (t - τ r₀)) + 1) -
            (N.reaction r₀).source.massActionMonomial (x t))) ≠
        κ.k r₀ * ((N.reaction r₀).source.massActionMonomial xs) *
          (Real.exp (delayLogRatio xs (N.reaction r₀).target (x t)) -
            Real.exp (delayLogRatio xs (N.reaction r₀).source (x t))) :=
      fun h => hne ((delayLyapunov_deriv_term_eq_bound_iff N κ τ hxs hpos t r₀).mp h)
    exact lt_of_le_of_ne hle hne''
  have hsum := Finset.sum_lt_sum (fun r _ => delayLyapunov_deriv_term_le N κ τ hxs hpos t r)
    ⟨r₀, Finset.mem_univ r₀, hlt0⟩
  have hle' : N.delayLyapunovDeriv κ τ (xs := xs) x t ≤
      (∑ r, κ.k r * ((N.reaction r).source.massActionMonomial xs) *
        (Real.exp (delayLogRatio xs (N.reaction r).target (x t)) -
          Real.exp (delayLogRatio xs (N.reaction r).source (x t)))) :=
    Finset.sum_le_sum fun r _ => delayLyapunov_deriv_term_le N κ τ hxs hpos t r
  unfold delayLyapunovDeriv
  linarith

/-- **The vanishing of the derivative.**  The derivative of the Lyapunov–Krasovskii functional
vanishes exactly when the monomial ratio of the source complex at the delayed time agrees with
the monomial ratio of the target complex at the current time, for every reaction. -/
theorem delayLyapunov_deriv_eq_zero_iff
    (N : Network S) (κ : N.RateConstants) (τ : N.R → ℝ) {xs : Concentration S}
    (hxs : xs.Positive) (hcb : N.IsComplexBalanced κ xs)
    {x : ℝ → Concentration S} (hpos : ∀ t, (x t).Positive) (t : ℝ) :
    N.delayLyapunovDeriv κ τ (xs := xs) x t = 0 ↔
      ∀ r, delayRatio xs (N.reaction r).source (x (t - τ r))
        = delayRatio xs (N.reaction r).target (x t) := by
  have hsumU : (∑ r, κ.k r * ((N.reaction r).source.massActionMonomial xs) *
      (Real.exp (delayLogRatio xs (N.reaction r).target (x t)) -
        Real.exp (delayLogRatio xs (N.reaction r).source (x t)))) = 0 := by
    have hker := (N.isComplexBalanced_iff_kineticMap κ xs).mp hcb
    have hpair := N.sum_kineticMap_mul κ (N.complexMonomialVector xs)
      (fun c => Real.exp (delayLogRatio xs c.val (x t)))
    rw [hker] at hpair
    simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero] at hpair
    rw [hpair]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp [sourceIdx, targetIdx]
  constructor
  · intro hzero
    unfold delayLyapunovDeriv at hzero
    -- the gap between the bound and the term is nonnegative
    have hgap : ∀ r ∈ Finset.univ,
        0 ≤ (κ.k r * ((N.reaction r).source.massActionMonomial xs) *
              (Real.exp (delayLogRatio xs (N.reaction r).target (x t)) -
                Real.exp (delayLogRatio xs (N.reaction r).source (x t)))) -
            (κ.k r * ((N.reaction r).source.massActionMonomial (x (t - τ r)) *
              (delayLogRatio xs (N.reaction r).target (x t) -
                delayLogRatio xs (N.reaction r).source (x (t - τ r)) + 1) -
              (N.reaction r).source.massActionMonomial (x t))) := by
      intro r _
      have hle := delayLyapunov_deriv_term_le N κ τ hxs hpos t r
      linarith
    have hgapsum : ∑ r, ((κ.k r * ((N.reaction r).source.massActionMonomial xs) *
              (Real.exp (delayLogRatio xs (N.reaction r).target (x t)) -
                Real.exp (delayLogRatio xs (N.reaction r).source (x t)))) -
            (κ.k r * ((N.reaction r).source.massActionMonomial (x (t - τ r)) *
              (delayLogRatio xs (N.reaction r).target (x t) -
                delayLogRatio xs (N.reaction r).source (x (t - τ r)) + 1) -
              (N.reaction r).source.massActionMonomial (x t)))) = 0 := by
      rw [Finset.sum_sub_distrib, hsumU, hzero, sub_zero]
    have heach := (Finset.sum_eq_zero_iff_of_nonneg hgap).mp hgapsum
    intro r
    have hr := heach r (Finset.mem_univ r)
    -- the gap vanishes, so the term equals its bound
    have hEq : (κ.k r *
          ((N.reaction r).source.massActionMonomial (x (t - τ r)) *
            (delayLogRatio xs (N.reaction r).target (x t) -
              delayLogRatio xs (N.reaction r).source (x (t - τ r)) + 1) -
            (N.reaction r).source.massActionMonomial (x t))) =
        κ.k r * ((N.reaction r).source.massActionMonomial xs) *
          (Real.exp (delayLogRatio xs (N.reaction r).target (x t)) -
            Real.exp (delayLogRatio xs (N.reaction r).source (x t))) := by
      linarith
    exact (delayLyapunov_deriv_term_eq_bound_iff N κ τ hxs hpos t r).mp hEq
  · intro hrat
    have htermeq : ∀ r, (κ.k r *
          ((N.reaction r).source.massActionMonomial (x (t - τ r)) *
            (delayLogRatio xs (N.reaction r).target (x t) -
              delayLogRatio xs (N.reaction r).source (x (t - τ r)) + 1) -
            (N.reaction r).source.massActionMonomial (x t))) =
        κ.k r * ((N.reaction r).source.massActionMonomial xs) *
          (Real.exp (delayLogRatio xs (N.reaction r).target (x t)) -
            Real.exp (delayLogRatio xs (N.reaction r).source (x t))) :=
      fun r => (delayLyapunov_deriv_term_eq_bound_iff N κ τ hxs hpos t r).mpr (hrat r)
    unfold delayLyapunovDeriv
    have hconv : (∑ r, κ.k r *
          ((N.reaction r).source.massActionMonomial (x (t - τ r)) *
            (delayLogRatio xs (N.reaction r).target (x t) -
              delayLogRatio xs (N.reaction r).source (x (t - τ r)) + 1) -
            (N.reaction r).source.massActionMonomial (x t))) =
        ∑ r, κ.k r * ((N.reaction r).source.massActionMonomial xs) *
          (Real.exp (delayLogRatio xs (N.reaction r).target (x t)) -
            Real.exp (delayLogRatio xs (N.reaction r).source (x t))) := by
      refine Finset.sum_congr rfl fun r _ => ?_
      exact htermeq r
    rw [hconv]
    exact hsumU

/-! ### From ratio constancy to complex balance -/

/-- **Ratio constancy across the reactions forces complex balance.**  If the monomial ratios of
the source and the target complexes agree along every reaction at the concentration `z`, then the
logarithmic dissipation of the mass-action field at `z` vanishes, and `z` is complex balanced with
respect to the complex-balanced reference `xs`. -/
theorem complexBalanced_of_ratio_const (N : Network S) (κ : N.RateConstants)
    {xs z : Concentration S} (hxs : xs.Positive) (hcb : N.IsComplexBalanced κ xs)
    (hz : z.Positive)
    (hconst : ∀ r, delayRatio xs (N.reaction r).source z
        = delayRatio xs (N.reaction r).target z) :
    N.IsComplexBalanced κ z := by
  have hdiss : (∑ s, (Real.log (z s) - Real.log (xs s)) * N.massActionVectorField κ z s) = 0 := by
    rw [massActionVectorField_pairing]
    have hpair : ∀ c : N.ComplexIdx,
        (∑ s, (c.val s : ℝ) * (Real.log (z s) - Real.log (xs s)))
          = Real.log (N.complexMonomialVector z c) - Real.log (N.complexMonomialVector xs c) := by
      intro c
      rw [log_complexMonomialVector N hz, log_complexMonomialVector N hxs, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun s _ => by ring
    simp only [hpair]
    rw [kineticMap_pairing N κ (N.complexMonomialVector z)
      (fun c => Real.log (N.complexMonomialVector z c) - Real.log (N.complexMonomialVector xs c))]
    apply Finset.sum_eq_zero
    intro r _
    have hLsrc : Real.log (N.complexMonomialVector z (N.sourceIdx r))
          - Real.log (N.complexMonomialVector xs (N.sourceIdx r))
        = delayLogRatio xs (N.reaction r).source z := by
      have hAe := massActionMonomial_eq_mul_exp_logRatio hxs hz (N.reaction r).source
      have hms0 : 0 < (N.reaction r).source.massActionMonomial xs :=
        Complex.massActionMonomial_pos hxs _
      show Real.log ((N.reaction r).source.massActionMonomial z) -
          Real.log ((N.reaction r).source.massActionMonomial xs) = _
      rw [hAe, Real.log_mul hms0.ne' (Real.exp_pos _).ne', Real.log_exp]
      ring
    have hLtgt : Real.log (N.complexMonomialVector z (N.targetIdx r))
          - Real.log (N.complexMonomialVector xs (N.targetIdx r))
        = delayLogRatio xs (N.reaction r).target z := by
      have hAe := massActionMonomial_eq_mul_exp_logRatio hxs hz (N.reaction r).target
      have hms0 : 0 < (N.reaction r).target.massActionMonomial xs :=
        Complex.massActionMonomial_pos hxs _
      show Real.log ((N.reaction r).target.massActionMonomial z) -
          Real.log ((N.reaction r).target.massActionMonomial xs) = _
      rw [hAe, Real.log_mul hms0.ne' (Real.exp_pos _).ne', Real.log_exp]
      ring
    have hlog : Real.log (delayRatio xs (N.reaction r).source z)
        = Real.log (delayRatio xs (N.reaction r).target z) :=
      congrArg Real.log (hconst r)
    rw [hLsrc, hLtgt]
    rw [← log_delayRatio_eq_delayLogRatio hxs (N.reaction r).source hz]
    rw [← log_delayRatio_eq_delayLogRatio hxs (N.reaction r).target hz]
    rw [hlog]
    ring
  exact complexBalanced_of_dissipation_eq_zero N κ hz hxs hcb hdiss

/-! ### The strict decrease away from the steady states -/

/-- **Strict decrease away from the steady states.**  Let `xs` be a positive detailed-balanced
concentration, and let `x` be a positive solution segment.  Suppose that at time `t` the solution
segment is *ratio consistent*: for every reaction the monomial ratio of the source complex at the
delayed time agrees with the monomial ratio of the source complex at the current time.  Then the
derivative of the Lyapunov–Krasovskii functional at `t` is strictly negative unless `x t` is a
mass-action steady state.

The consistency hypothesis is automatic when there is no delay (`τ ≡ 0`); for a genuine delay it
is the natural "the segment does not change the ratios" condition. -/
theorem delayLyapunov_deriv_neg_of_not_steady
    (N : Network S) (κ : N.RateConstants) (τ : N.R → ℝ) {xs : Concentration S}
    (hxs : xs.Positive) (hdb : N.IsDetailedBalanced κ xs)
    {x : ℝ → Concentration S} (hpos : ∀ t, (x t).Positive) (t : ℝ)
    (hcons : ∀ r, delayRatio xs (N.reaction r).source (x (t - τ r))
        = delayRatio xs (N.reaction r).source (x t))
    (hns : ¬ N.IsMassActionSteadyState κ (x t)) :
    N.delayLyapunovDeriv κ τ (xs := xs) x t < 0 := by
  have hcb : N.IsComplexBalanced κ xs := N.isComplexBalanced_of_isDetailedBalanced κ xs hdb
  have hnonpos : N.delayLyapunovDeriv κ τ (xs := xs) x t ≤ 0 := by
    have h := delayLyapunov_deriv_nonpos N κ τ hxs hcb hpos t
    unfold delayLyapunovDeriv
    exact h
  by_contra hcon
  have hzero : N.delayLyapunovDeriv κ τ (xs := xs) x t = 0 :=
    le_antisymm hnonpos (not_lt.mp hcon)
  have hrat : ∀ r, delayRatio xs (N.reaction r).source (x (t - τ r))
      = delayRatio xs (N.reaction r).target (x t) :=
    (delayLyapunov_deriv_eq_zero_iff N κ τ hxs hcb hpos t).mp hzero
  have hrat' : ∀ r, delayRatio xs (N.reaction r).source (x t)
      = delayRatio xs (N.reaction r).target (x t) := fun r => (hcons r).symm.trans (hrat r)
  have hcbx : N.IsComplexBalanced κ (x t) :=
    complexBalanced_of_ratio_const N κ hxs hcb (hpos t) hrat'
  exact absurd (hcbx.isMassActionSteadyState N κ) hns

/-- **Strict decrease away from the steady states, without delay.**  With `τ ≡ 0` the ratio
consistency is automatic, and the Lyapunov–Krasovskii functional is the Horn–Jackson entropy of the
instantaneous mass-action field. -/
theorem delayLyapunov_deriv_neg_of_not_steady_noDelay
    (N : Network S) (κ : N.RateConstants) (τ : N.R → ℝ) {xs : Concentration S}
    (hxs : xs.Positive) (hdb : N.IsDetailedBalanced κ xs)
    {x : ℝ → Concentration S} (hpos : ∀ t, (x t).Positive) (t : ℝ)
    (hτ0 : ∀ r, τ r = 0)
    (hns : ¬ N.IsMassActionSteadyState κ (x t)) :
    N.delayLyapunovDeriv κ τ (xs := xs) x t < 0 := by
  refine delayLyapunov_deriv_neg_of_not_steady N κ τ hxs hdb hpos t ?_ hns
  intro r
  simp [hτ0 r]

/-- **The classical strict entropy production.**  Relative to a positive complex-balanced
reference `xs`, the logarithmic dissipation `⟨log(x/x*), f(x)⟩` of the *instantaneous* mass-action
field vanishes exactly at the complex-balanced concentrations, hence it is strictly negative at
every concentration that is not a steady state.  This is the classical statement that the delayed
functional specialises to when there is no delay. -/
theorem delayEntropy_dissipation_neg_of_not_steady
    (N : Network S) (κ : N.RateConstants) {xs x : Concentration S}
    (hxs : xs.Positive) (hcb : N.IsComplexBalanced κ xs) (hx : x.Positive)
    (hns : ¬ N.IsMassActionSteadyState κ x) :
    (∑ s, (Real.log (x s) - Real.log (xs s)) * N.massActionVectorField κ x s) < 0 := by
  have hnonpos := dissipation_nonpos N κ hx hxs hcb
  by_contra hcon
  have hz : (∑ s, (Real.log (x s) - Real.log (xs s)) * N.massActionVectorField κ x s) = 0 :=
    le_antisymm hnonpos (not_lt.mp hcon)
  have hcbx : N.IsComplexBalanced κ x := complexBalanced_of_dissipation_eq_zero N κ hx hxs hcb hz
  exact absurd (hcbx.isMassActionSteadyState N κ) hns

/-! ### Boundedness below and convergence of the functional -/

omit [DecidableEq S] in
/-- **The logarithmic ratio is the logarithm of the monomial ratio.** -/
theorem delayLogRatio_eq_log_div {xs : Concentration S} (hxs : xs.Positive) (c : Complex S)
    {z : Concentration S} (hz : z.Positive) :
    delayLogRatio xs c z = Real.log (c.massActionMonomial z / c.massActionMonomial xs) := by
  have h := massActionMonomial_eq_mul_exp_logRatio hxs hz c
  rw [Real.log_div (Complex.massActionMonomial_pos hz _).ne'
    (Complex.massActionMonomial_pos hxs _).ne']
  rw [h, Real.log_mul (Complex.massActionMonomial_pos hxs _).ne' (Real.exp_pos _).ne', Real.log_exp]
  ring

/-- **The functional is nonnegative.**  For nonnegative delays the Lyapunov–Krasovskii functional
is a sum of Gibbs-type nonnegative terms: the Horn–Jackson entropy of the current state and the
delay integrals of the nonnegative integrands `g_r`.  In particular the functional is bounded
below. -/
theorem delayLyapunov_nonneg (N : Network S) (κ : N.RateConstants) (τ : N.R → ℝ)
    {xs : Concentration S} (hxs : xs.Positive) {x : ℝ → Concentration S}
    (hpos : ∀ t, (x t).Positive) (hτ : ∀ r, 0 ≤ τ r) (t : ℝ) :
    0 ≤ N.delayLyapunov κ τ xs x t := by
  unfold delayLyapunov
  have hent : 0 ≤ delayEntropy xs (x t) := by
    unfold delayEntropy
    refine Finset.sum_nonneg fun s _ => ?_
    have h := relEntropyTerm_nonneg (hpos t s).le (hxs s)
    rw [Real.log_div (hpos t s).ne' (hxs s).ne'] at h
    linarith
  have hdel : 0 ≤ ∑ r, κ.k r * ∫ u in (t - τ r)..t, N.delayIntegrand xs r (x u) := by
    refine Finset.sum_nonneg fun r _ => ?_
    have hk : 0 ≤ κ.k r := (κ.positive r).le
    have hint : 0 ≤ ∫ u in (t - τ r)..t, N.delayIntegrand xs r (x u) := by
      refine intervalIntegral.integral_nonneg ?_ ?_
      · linarith [hτ r]
      · intro u _
        have hmono := relEntropyTerm_nonneg
          (Complex.massActionMonomial_nonneg (hpos u).nonnegative (N.reaction r).source)
          (Complex.massActionMonomial_pos hxs (N.reaction r).source)
        unfold delayIntegrand
        rw [delayLogRatio_eq_log_div hxs (N.reaction r).source (hpos u)]
        linarith
    exact mul_nonneg hk hint
  linarith

/-- **The functional converges along a positive solution.**  The Lyapunov–Krasovskii functional is
nonincreasing and bounded below, hence it converges to a limit. -/
theorem delayLyapunov_tendsto (N : Network S) (κ : N.RateConstants) (τ : N.R → ℝ)
    {xs : Concentration S} (hxs : xs.Positive) (hcb : N.IsComplexBalanced κ xs)
    {x : ℝ → Concentration S} (hx : N.IsDelaySolution κ τ x) (hpos : ∀ t, (x t).Positive)
    (hτ : ∀ r, 0 ≤ τ r) :
    ∃ c : ℝ, Tendsto (N.delayLyapunov κ τ xs x) atTop (𝓝 c) := by
  have hanti : Antitone (N.delayLyapunov κ τ xs x) :=
    delayLyapunov_antitone N κ τ hxs hcb hx hpos
  have hnonneg : ∀ t, 0 ≤ N.delayLyapunov κ τ xs x t := delayLyapunov_nonneg N κ τ hxs hpos hτ
  have hbdd : BddBelow (Set.range (N.delayLyapunov κ τ xs x)) :=
    ⟨0, fun y ⟨t, h⟩ => by rw [← h]; exact hnonneg t⟩
  exact ⟨⨅ t, N.delayLyapunov κ τ xs x t, tendsto_atTop_ciInf hanti hbdd⟩

/-! ### The LaSalle part -/

/-- **A convergent differentiable function has vanishing derivative at `+∞`.**  If `f` converges at
`+∞` and its derivative converges to `c`, then `c = 0`: the mean value theorem turns a window of
length one into the derivative at some point of the window, and the displacement over the window
tends to `0`. -/
theorem tendsto_deriv_eq_zero_of_tendsto {fderiv : ℝ → ℝ} {f : ℝ → ℝ} {L c : ℝ}
    (hf : Tendsto f atTop (𝓝 L)) (hfd : ∀ t, HasDerivAt f (fderiv t) t)
    (hderiv : Tendsto fderiv atTop (𝓝 c)) : c = 0 := by
  have hMVT : ∀ t, ∃ ξ ∈ Set.Ioo t (t + 1), f (t + 1) - f t = fderiv ξ := by
    intro t
    obtain ⟨ξ, hξ, hξ'⟩ := exists_hasDerivAt_eq_slope f fderiv (a := t) (b := t + 1)
      (by norm_num)
      (fun u _ => (hfd u).continuousAt.continuousWithinAt)
      (fun u _ => hfd u)
    refine ⟨ξ, hξ, ?_⟩
    have h1 : (t + 1) - t = 1 := by ring
    rw [h1, div_one] at hξ'
    linarith
  set ξ : ℝ → ℝ := fun t => Classical.choose (hMVT t) with hξdef
  have hξmem : ∀ t, ξ t ∈ Set.Ioo t (t + 1) := fun t => (Classical.choose_spec (hMVT t)).1
  have hξeq : ∀ t, f (t + 1) - f t = fderiv (ξ t) := fun t => (Classical.choose_spec (hMVT t)).2
  -- the displacement over a window of length one tends to zero
  have hdisp : Tendsto (fun t => f (t + 1) - f t) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t => f (t + 1)) atTop (𝓝 L) :=
      hf.comp (atTop.tendsto_atTop_add_const_right 1 tendsto_id)
    have h2 : Tendsto (fun t => f t) atTop (𝓝 L) := hf
    simpa using h1.sub h2
  -- the mean value points escape to infinity
  have hξmono : Tendsto ξ atTop atTop :=
    tendsto_atTop_mono (fun t => (hξmem t).1.le) tendsto_id
  have h3 : Tendsto (fun t => fderiv (ξ t)) atTop (𝓝 c) := hderiv.comp hξmono
  have h4 : Tendsto (fun t => fderiv (ξ t)) atTop (𝓝 0) := by
    refine Tendsto.congr' ?_ hdisp
    filter_upwards [] with t
    exact hξeq t
  exact tendsto_nhds_unique h3 h4

omit [DecidableEq S] in
/-- **Continuity of the mass-action monomial.** -/
theorem continuous_massActionMonomial (c : Complex S) :
    Continuous (fun x : Concentration S => c.massActionMonomial x) := by
  unfold Complex.massActionMonomial
  exact continuous_finsetProd _ fun s _ => (continuous_apply s).pow _

/-- **Every limit of a delay solution is a mass-action steady state.**  A solution of the delay
system that converges cannot converge to a non-equilibrium: the displacement over a window of
length one tends to `0`, while the (continuous) delay field at the limit is the *instantaneous*
mass-action field at the limit.  This is the structural fact behind the LaSalle argument: the
ω-limit set of a delay solution consists of equilibria. -/
theorem delay_limit_isSteadyState (N : Network S) (κ : N.RateConstants) (τ : N.R → ℝ)
    {x : ℝ → Concentration S} (hx : N.IsDelaySolution κ τ x)
    (y : Concentration S) (hy : Tendsto x atTop (𝓝 y)) :
    N.IsMassActionSteadyState κ y := by
  intro s
  -- the delay field tends to the instantaneous field at the limit
  have hfield : Tendsto (fun t => N.delayField κ τ x t s) atTop (𝓝 (N.massActionVectorField κ y s)) := by
    have hdel : ∀ r, Tendsto (fun t => x (t - τ r)) atTop (𝓝 y) := by
      intro r
      refine hy.comp ?_
      exact atTop.tendsto_atTop_add_const_right (-τ r) tendsto_id
    have hmono : ∀ r, Tendsto (fun t => (N.reaction r).source.massActionMonomial (x (t - τ r)))
        atTop (𝓝 ((N.reaction r).source.massActionMonomial y)) :=
      fun r => (continuous_massActionMonomial _).continuousAt.tendsto.comp (hdel r)
    have hmono0 : ∀ r, Tendsto (fun t => (N.reaction r).source.massActionMonomial (x t))
        atTop (𝓝 ((N.reaction r).source.massActionMonomial y)) :=
      fun r => (continuous_massActionMonomial _).continuousAt.tendsto.comp hy
    have hsum : Tendsto (fun t => ∑ r, κ.k r *
          ((N.reaction r).source.massActionMonomial (x (t - τ r)) * ((N.reaction r).target s : ℝ) -
            (N.reaction r).source.massActionMonomial (x t) * ((N.reaction r).source s : ℝ)))
        atTop (𝓝 (∑ r, κ.k r *
          ((N.reaction r).source.massActionMonomial y * ((N.reaction r).target s : ℝ) -
            (N.reaction r).source.massActionMonomial y * ((N.reaction r).source s : ℝ)))) := by
      refine tendsto_finsetSum Finset.univ fun r _ => ?_
      have h1 : Tendsto (fun t => (N.reaction r).source.massActionMonomial (x (t - τ r)))
          atTop (𝓝 ((N.reaction r).source.massActionMonomial y)) := hmono r
      have h2 : Tendsto (fun t => (N.reaction r).source.massActionMonomial (x t))
          atTop (𝓝 ((N.reaction r).source.massActionMonomial y)) := hmono0 r
      have h1' : Tendsto (fun t => (N.reaction r).source.massActionMonomial (x (t - τ r)) *
            ((N.reaction r).target s : ℝ)) atTop
          (𝓝 ((N.reaction r).source.massActionMonomial y * ((N.reaction r).target s : ℝ))) :=
        h1.mul_const _
      have h2' : Tendsto (fun t => (N.reaction r).source.massActionMonomial (x t) *
            ((N.reaction r).source s : ℝ)) atTop
          (𝓝 ((N.reaction r).source.massActionMonomial y * ((N.reaction r).source s : ℝ))) :=
        h2.mul_const _
      have h3 : Tendsto (fun t => (N.reaction r).source.massActionMonomial (x (t - τ r)) *
            ((N.reaction r).target s : ℝ) -
            (N.reaction r).source.massActionMonomial (x t) * ((N.reaction r).source s : ℝ)) atTop
          (𝓝 ((N.reaction r).source.massActionMonomial y * ((N.reaction r).target s : ℝ) -
            (N.reaction r).source.massActionMonomial y * ((N.reaction r).source s : ℝ))) :=
        h1'.sub h2'
      exact tendsto_const_nhds.mul h3
    have hval : (∑ r, κ.k r *
          ((N.reaction r).source.massActionMonomial y * ((N.reaction r).target s : ℝ) -
            (N.reaction r).source.massActionMonomial y * ((N.reaction r).source s : ℝ))) =
        N.massActionVectorField κ y s := by
      rw [massActionVectorField_apply]
      simp only [massActionRate_eq]
      refine Finset.sum_congr rfl fun r _ => ?_
      simp only [reactionVector_apply]
      have hcm : N.complexMonomialVector y (N.sourceIdx r)
          = (N.reaction r).source.massActionMonomial y := rfl
      rw [hcm]
      ring
    have : Tendsto (fun t => N.delayField κ τ x t s) atTop
        (𝓝 (N.massActionVectorField κ y s)) := by
      have hdef : (fun t => N.delayField κ τ x t s) =
          (fun t => ∑ r, κ.k r *
            ((N.reaction r).source.massActionMonomial (x (t - τ r)) * ((N.reaction r).target s : ℝ) -
              (N.reaction r).source.massActionMonomial (x t) * ((N.reaction r).source s : ℝ))) := by
        funext t
        rfl
      rw [hdef]
      simpa [hval] using hsum
    exact this
  -- the coordinate converges
  have hcoord0 : Tendsto (fun t => x t s) atTop (𝓝 (y s)) :=
    (tendsto_pi_nhds.1 hy) s
  -- the derivative of the coordinate is the delay field
  have hcoord : ∀ t, HasDerivAt (fun t => x t s) (N.delayField κ τ x t s) t :=
    fun t => (hasDerivAt_pi.mp (hx t)) s
  have hzero := tendsto_deriv_eq_zero_of_tendsto (f := fun t => x t s)
    (fderiv := fun t => N.delayField κ τ x t s) (L := y s)
    (c := N.massActionVectorField κ y s) hcoord0 hcoord hfield
  exact hzero

/-- **The trajectory approaches the steady states.**  Let `x` be a solution of the delay system
whose range is relatively compact, and suppose that every accumulation point of the trajectory at
infinity (its ω-limit set) is a mass-action steady state.  Then the distance from the trajectory
to the set of mass-action steady states tends to zero: the ω-limit set lies in the steady states,
and the trajectory cannot stay away from them.

This is the LaSalle conclusion in ω-limit-set form.  To upgrade it to a *convergence* statement one
needs the ω-limit set to be a singleton (`delay_semistability`) or a uniqueness theorem for the
steady states in the delayed compatibility class, which is not available here. -/
theorem delay_semistability_of_omegaLimit (N : Network S) (κ : N.RateConstants) (τ : N.R → ℝ)
    {x : ℝ → Concentration S} (_hx : N.IsDelaySolution κ τ x)
    (hcompact : IsCompact (closure (Set.range x)))
    (hω : ∀ z, ClusterPt z (Filter.map x atTop) → N.IsMassActionSteadyState κ z) :
    Tendsto (fun t => Metric.infDist (x t) {z : Concentration S | N.IsMassActionSteadyState κ z})
      atTop (𝓝 0) := by
  set E : Set (Concentration S) := {z | N.IsMassActionSteadyState κ z} with hE
  have hEclosed : IsClosed E := by
    have heq : E = ⋂ s, {z : Concentration S | N.massActionVectorField κ z s = 0} := by
      ext z
      simp only [hE, Set.mem_ofPred_eq, Set.mem_iInter]
      constructor
      · intro h s
        exact h s
      · intro h s
        exact h s
    rw [heq]
    exact isClosed_iInter fun s =>
      isClosed_eq
        ((continuous_apply s : Continuous (fun p : Concentration S => p s)).comp
          (N.massActionVectorField_contDiff κ (n := 0)).continuous)
        continuous_const
  have hcont : Continuous (fun z : Concentration S => Metric.infDist z E) :=
    Metric.continuous_infDist_pt E
  refine (Metric.tendsto_atTop).2 ?_
  intro ε hε
  by_contra hcon
  -- there are arbitrarily large times at distance at least `ε` from the steady states
  have hfar' : ∀ N, ∃ t ≥ N, ε ≤ Metric.infDist (x t) E := by
    intro N
    by_contra h
    have h' : ∀ t, N ≤ t → ¬ (ε ≤ Metric.infDist (x t) E) := by
      intro t hN
      by_contra ht
      exact h ⟨t, hN, ht⟩
    have hh : ∀ᶠ t in atTop, (dist (Metric.infDist (x t) E) 0 < ε) := by
      refine Filter.eventually_atTop.mpr ⟨N, ?_⟩
      intro t hN
      have h0 : 0 ≤ Metric.infDist (x t) E := Metric.infDist_nonneg
      have hd : dist (Metric.infDist (x t) E) 0 = Metric.infDist (x t) E := by
        rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr h0), sub_zero]
      rw [hd]
      exact lt_of_not_ge (h' t hN)
    exact hcon (Filter.eventually_atTop.mp hh)
  have hnot : ¬∀ᶠ t in atTop, ¬ (ε ≤ Metric.infDist (x t) E) := by
    intro hall
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hall
    obtain ⟨t, ht, hP⟩ := hfar' N
    exact hN t ht.le hP
  have hfar : ∃ᶠ t in atTop, ε ≤ Metric.infDist (x t) E := by
    have h2 : ¬∀ᶠ t in atTop, (¬ (ε ≤ Metric.infDist (x t) E)) := hnot
    simpa only [not_not] using Filter.not_eventually.mp h2
  -- a sequence of such times, escaping to infinity
  obtain ⟨tseq, htseq, hfar'⟩ := Filter.exists_seq_forall_of_frequently hfar
  -- a cluster point of the corresponding values
  obtain ⟨z, hzK, φ, hφmono, hconv⟩ :=
    IsCompact.tendsto_subseq (x := fun n => x (tseq n)) hcompact
      (fun n => subset_closure (show x (tseq n) ∈ Set.range x from ⟨tseq n, rfl⟩))
  -- the cluster point of the sequence is an accumulation point of the trajectory
  have hφtendsto : Tendsto φ atTop atTop := StrictMono.tendsto_atTop hφmono
  have hg : Tendsto (tseq ∘ φ) atTop atTop := htseq.comp hφtendsto
  have hzc : ClusterPt z (Filter.map x atTop) := by
    have hmap : MapClusterPt z atTop (x ∘ (tseq ∘ φ)) :=
      Filter.Tendsto.mapClusterPt hconv
    have : MapClusterPt z atTop x := MapClusterPt.of_comp hg hmap
    exact this
  -- the cluster point is far from the steady states, but it is a steady state
  set S : Set (Concentration S) := {z | ε ≤ Metric.infDist z E} with hS
  have hSclosed : IsClosed S :=
    IsClosed.preimage hcont (isClosed_Ici : IsClosed (Set.Ici ε))
  have hzS : z ∈ S := by
    have hmap : MapClusterPt z atTop (x ∘ (tseq ∘ φ)) :=
      Filter.Tendsto.mapClusterPt hconv
    have hmem : ∀ᶠ n in atTop, x (tseq (φ n)) ∈ S := by
      filter_upwards [] with n
      exact hfar' (φ n)
    have hzS' := IsClosed.mem_of_mapClusterPt hSclosed hmap hmem
    exact hzS'
  have hzE : z ∈ E := hω z hzc
  have hz0 : Metric.infDist z E = 0 := Metric.infDist_zero_of_mem hzE
  have hzfar : ε ≤ Metric.infDist z E := by
    have : z ∈ {z | ε ≤ Metric.infDist z E} := hzS
    exact Set.mem_ofPred_eq.mp this
  linarith

/-- **Semistability.**  Let `x` be a solution of the delay system whose range is relatively
compact, and suppose that its ω-limit set (the set of accumulation points of the range at
infinity) is a singleton `{y}`.  Then the solution converges to `y`, and `y` is a mass-action
steady state of the instantaneous field: the delay system is *semistable*, in the sense that every
trajectory approaches an equilibrium. -/
theorem delay_semistability (N : Network S) (κ : N.RateConstants) (τ : N.R → ℝ)
    {x : ℝ → Concentration S} (hx : N.IsDelaySolution κ τ x)
    (hcompact : IsCompact (closure (Set.range x)))
    (y : Concentration S)
    (huniq : ∀ z, ClusterPt z (Filter.map x atTop) → z = y) :
    Tendsto x atTop (𝓝 y) ∧ N.IsMassActionSteadyState κ y := by
  have hconv : Tendsto x atTop (𝓝 y) := by
    refine IsCompact.tendsto_nhds_of_unique_mapClusterPt hcompact ?_ ?_
    · filter_upwards [] with t
      exact subset_closure ⟨t, rfl⟩
    · intro z _ hzc
      exact huniq z hzc
  exact ⟨hconv, delay_limit_isSteadyState N κ τ hx y hconv⟩

end Network

end CRNT

/-! ### A concrete instance: the reversible pair `A ⇌ B` with a delay

The library's canonical deficiency-zero network `A ⇌ B` (`CRNT.Examples.ReversiblePair`) is used
as a delay network: the delay is an extra parameter `τ : R → ℝ`, attached to the channels.  The
positive concentration `(k₁, k₀)` is detailed balanced, hence a steady state and a constant
solution of the delayed system. -/

namespace CRNT.Examples.ReversiblePair

open CRNT

/-- A unit delay on both channels of the reversible pair. -/
def unitDelay : Rxn → ℝ := fun _ => 1

/-- **The equilibrium of the delayed reversible pair is detailed balanced.**  At `(k₁, k₀)` the
forward flux `k₀ · k₁` and the reverse flux `k₁ · k₀` coincide. -/
theorem equilibrium_detailedBalanced {k₀ k₁ : ℝ} (h₀ : 0 < k₀) (h₁ : 0 < k₁) :
    N.IsDetailedBalanced (rates h₀ h₁) (equilibrium k₀ k₁) :=
  N.isDetailedBalanced_of_reactionwiseDetailedBalanced revStruct _ _
    (equilibrium_isReactionwiseDetailedBalanced h₀ h₁)

/-- **The equilibrium is a solution of the delayed system.**  The constant trajectory at the
detailed-balanced concentration solves the delay system (`const_isDelaySolution_iff`). -/
theorem equilibrium_isDelaySolution {k₀ k₁ : ℝ} (h₀ : 0 < k₀) (h₁ : 0 < k₁) :
    N.IsDelaySolution (rates h₀ h₁) unitDelay (fun _ => equilibrium k₀ k₁) :=
  CRNT.Network.const_isDelaySolution_iff N _ _ _ |>.mpr (equilibrium_isSteadyState h₀ h₁)

/-- A positive concentration of the reversible pair. -/
def offEquilibrium : Concentration Species := fun _ => 2

/-- The concentration `(2, 2)` is strictly positive. -/
theorem offEquilibrium_positive : offEquilibrium.Positive := by
  intro s
  cases s <;> simp [offEquilibrium]

/-- The `A`-component of the mass-action field of the reversible pair at `(2, 2)` is
`2 (k₁ − k₀)`. -/
theorem offEquilibrium_field_A {k₀ k₁ : ℝ} (h₀ : 0 < k₀) (h₁ : 0 < k₁) :
    N.massActionVectorField (rates h₀ h₁) offEquilibrium Species.A = 2 * (k₁ - k₀) := by
  rw [N.massActionVectorField_apply]
  have huniv : (Finset.univ : Finset Rxn) = {Rxn.fwd, Rxn.bwd} := by decide
  show (∑ r : Rxn, N.massActionRate (rates h₀ h₁) r offEquilibrium
        * N.reactionVector r Species.A) = 2 * (k₁ - k₀)
  rw [huniv]
  simp [Finset.sum_insert, Finset.sum_singleton, CRNT.Network.massActionRate,
    CRNT.Network.reactionVector, N, rxn, cA, cB,
    Complex.massActionMonomial, offEquilibrium, rates, prod_univ_species]
  ring

/-- **The concentration `(2, 2)` is not a steady state** (unless the two rate constants agree). -/
theorem offEquilibrium_notSteadyState {k₀ k₁ : ℝ} (h₀ : 0 < k₀) (h₁ : 0 < k₁) (hne : k₀ ≠ k₁) :
    ¬ N.IsMassActionSteadyState (rates h₀ h₁) offEquilibrium := by
  intro h
  have hA := h Species.A
  rw [offEquilibrium_field_A h₀ h₁] at hA
  have hk : k₁ = k₀ := by linarith
  exact hne hk.symm

/-- **The strict decrease at a non-steady state (no delay).**  The derivative of the
Lyapunov–Krasovskii functional of the reversible pair at the positive non-equilibrium `(2, 2)` is
strictly negative. -/
theorem delayLyapunovDeriv_neg_at_offEquilibrium {k₀ k₁ : ℝ} (h₀ : 0 < k₀) (h₁ : 0 < k₁)
    (hne : k₀ ≠ k₁) :
    N.delayLyapunovDeriv (rates h₀ h₁) (fun _ => 0) (xs := equilibrium k₀ k₁)
      (fun _ => offEquilibrium) 0 < 0 :=
  Network.delayLyapunov_deriv_neg_of_not_steady_noDelay N (rates h₀ h₁) (fun _ => 0)
    (equilibrium_positive h₀ h₁) (equilibrium_detailedBalanced h₀ h₁)
    (fun _ => offEquilibrium_positive) 0 (by intro r; rfl)
    (offEquilibrium_notSteadyState h₀ h₁ hne)

/-- **The strict decrease at a non-steady state (with the unit delay).**  The same statement for
the delayed system: along the constant trajectory at `(2, 2)` the solution segment is ratio
consistent, so the derivative of the Lyapunov–Krasovskii functional is strictly negative. -/
theorem delayLyapunovDeriv_neg_at_offEquilibrium_delayed {k₀ k₁ : ℝ} (h₀ : 0 < k₀) (h₁ : 0 < k₁)
    (hne : k₀ ≠ k₁) :
    N.delayLyapunovDeriv (rates h₀ h₁) unitDelay (xs := equilibrium k₀ k₁)
      (fun _ => offEquilibrium) 0 < 0 :=
  Network.delayLyapunov_deriv_neg_of_not_steady N (rates h₀ h₁) unitDelay (equilibrium_positive h₀ h₁)
    (equilibrium_detailedBalanced h₀ h₁) (fun _ => offEquilibrium_positive) 0 (fun _ => rfl)
    (offEquilibrium_notSteadyState h₀ h₁ hne)

end CRNT.Examples.ReversiblePair
