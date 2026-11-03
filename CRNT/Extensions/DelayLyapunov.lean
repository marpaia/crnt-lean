import CRNT.Extensions.DelayMassAction
import CRNT.Dynamics.KineticMapPairing
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The Lyapunov–Krasovskii functional of a complex-balanced delay system

Lipták, Hangos, Pituk and Szederkényi (*Semistability of complex balanced kinetic systems with
arbitrary time delays*, Systems Control Lett. 114, 2018) extend the Horn–Jackson entropy to delay
mass-action systems `ẋ(t) = ∑_r κ_r (x(t − τ_r)^{y_r} y'_r − x(t)^{y_r} y_r)`. With a positive
complex-balanced equilibrium `x*`, `μ = log x − log x*`, `L_c = ⟨c, μ⟩`, and
`g_r(u) = x(u)^{y_r} (L_{y_r}(u) − 1) + x*^{y_r}`, the functional

`V(t) = ∑_s (x_s (μ_s − 1) + x*_s) + ∑_r κ_r ∫_{t − τ_r}^{t} g_r(u) du`

is nonincreasing along every positive solution. Its derivative is
`∑_r κ_r (x(t − τ_r)^{y_r} (L_{y'_r}(t) − L_{y_r}(t − τ_r) + 1) − x(t)^{y_r})`; the inequality
`a (log b − log a + 1) ≤ b` bounds it by `∑_r κ_r x*^{y_r} (e^{L_{y'_r}(t)} − e^{L_{y_r}(t)})`,
which vanishes by complex balance at `x*`.

* `delayLyapunov_hasDerivAt`: the derivative formula.
* `delayLyapunov_deriv_nonpos`: the derivative is `≤ 0`.
* `delayLyapunov_antitone`: `V` is nonincreasing.
-/

namespace CRNT

namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The Horn–Jackson entropy term of the functional. -/
noncomputable def delayEntropy (xs : Concentration S) (z : Concentration S) : ℝ :=
  ∑ s, (z s * (Real.log (z s) - Real.log (xs s) - 1) + xs s)

/-- `L_c(z) = ∑_s c_s (log z_s − log x*_s)`. -/
noncomputable def delayLogRatio (xs : Concentration S) (c : Complex S) (z : Concentration S) : ℝ :=
  ∑ s, (c s : ℝ) * (Real.log (z s) - Real.log (xs s))

/-- The integrand of the delay part for reaction `r`. -/
noncomputable def delayIntegrand (N : Network S) (xs : Concentration S) (r : N.R)
    (z : Concentration S) : ℝ :=
  (N.reaction r).source.massActionMonomial z * (delayLogRatio xs (N.reaction r).source z - 1) +
    (N.reaction r).source.massActionMonomial xs

/-- **The Lyapunov–Krasovskii functional.** -/
noncomputable def delayLyapunov (N : Network S) (κ : RateConstants N) (τ : N.R → ℝ)
    (xs : Concentration S) (x : ℝ → Concentration S) (t : ℝ) : ℝ :=
  delayEntropy xs (x t) + ∑ r, κ.k r * ∫ u in (t - τ r)..t, N.delayIntegrand xs r (x u)

omit [DecidableEq S] in
/-- A monomial at a positive state, relative to `x*`. -/
theorem massActionMonomial_eq_mul_exp_logRatio {xs z : Concentration S} (hxs : xs.Positive)
    (hz : z.Positive) (c : Complex S) :
    c.massActionMonomial z = c.massActionMonomial xs * Real.exp (delayLogRatio xs c z) := by
  have hexp : ∀ w : Concentration S, w.Positive →
      c.massActionMonomial w = Real.exp (∑ s, (c s : ℝ) * Real.log (w s)) := by
    intro w hw
    rw [Real.exp_sum, Complex.massActionMonomial]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (hw s), mul_comm]
  rw [hexp z hz, hexp xs hxs, ← Real.exp_add, delayLogRatio]
  congr 1
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun s _ => by ring

theorem delayLyapunov_hasDerivAt (N : Network S) (κ : RateConstants N) (τ : N.R → ℝ)
    {xs : Concentration S} {x : ℝ → Concentration S}
    (hx : N.IsDelaySolution κ τ x) (hpos : ∀ t, (x t).Positive) (t : ℝ) :
    HasDerivAt (N.delayLyapunov κ τ xs x)
      (∑ r, κ.k r * ((N.reaction r).source.massActionMonomial (x (t - τ r)) *
          (delayLogRatio xs (N.reaction r).target (x t) -
            delayLogRatio xs (N.reaction r).source (x (t - τ r)) + 1) -
        (N.reaction r).source.massActionMonomial (x t))) t := by
  have hxc : Continuous x := continuous_iff_continuousAt.2 fun t => (hx t).continuousAt
  have hcoord : ∀ s t, HasDerivAt (fun t => x t s) (N.delayField κ τ x t s) t :=
    fun s t => (hasDerivAt_pi.mp (hx t)) s
  have hlogc : ∀ s, Continuous fun u => Real.log (x u s) :=
    fun s => ((continuous_apply s).comp hxc).log fun u => (hpos u s).ne'
  -- continuity of the integrands
  have hgc : ∀ r, Continuous fun u => N.delayIntegrand xs r (x u) := by
    intro r
    unfold delayIntegrand delayLogRatio Complex.massActionMonomial
    refine ((continuous_finsetProd _ fun s _ => ((continuous_apply s).comp hxc).pow _).mul
      ((continuous_finsetSum _ fun s _ => continuous_const.mul
        ((hlogc s).sub continuous_const)).sub continuous_const)).add continuous_const
  set g : N.R → ℝ → ℝ := fun r u => N.delayIntegrand xs r (x u) with hg
  have hint : ∀ r, HasDerivAt (fun t => ∫ u in (t - τ r)..t, g r u) (g r t - g r (t - τ r)) t := by
    intro r
    have hG := fun t => ((hgc r).integral_hasStrictDerivAt 0 t).hasDerivAt
    have hsplit : (fun t => ∫ u in (t - τ r)..t, g r u) =
        fun t => (∫ u in (0 : ℝ)..t, g r u) - ∫ u in (0 : ℝ)..(t - τ r), g r u := by
      funext t
      rw [intervalIntegral.integral_interval_sub_left
        ((hgc r).intervalIntegrable _ _) ((hgc r).intervalIntegrable _ _)]
    rw [hsplit]
    exact (hG t).sub (HasDerivAt.comp_sub_const t (τ r) (hG (t - τ r)))
  -- the entropy part
  have hent : HasDerivAt (fun t => delayEntropy xs (x t))
      (∑ s, N.delayField κ τ x t s * (Real.log (x t s) - Real.log (xs s))) t := by
    unfold delayEntropy
    refine HasDerivAt.fun_sum fun s _ => ?_
    have hl := (hcoord s t).log (hpos t s).ne'
    have hp := ((hcoord s t).mul ((hl.sub_const (Real.log (xs s))).sub_const 1)).add_const (xs s)
    refine hp.congr_deriv ?_
    field_simp [(hpos t s).ne']
    ring
  have hsum : HasDerivAt (fun t => ∑ r, κ.k r * ∫ u in (t - τ r)..t, g r u)
      (∑ r, κ.k r * (g r t - g r (t - τ r))) t :=
    HasDerivAt.fun_sum (u := Finset.univ) fun r _ => (hint r).const_mul (κ.k r)
  have htot := hent.fun_add hsum
  unfold delayLyapunov
  refine htot.congr_deriv ?_
  -- algebra
  have e1 : ∑ s, N.delayField κ τ x t s * (Real.log (x t s) - Real.log (xs s)) =
      ∑ r, κ.k r * ((N.reaction r).source.massActionMonomial (x (t - τ r)) *
          delayLogRatio xs (N.reaction r).target (x t) -
        (N.reaction r).source.massActionMonomial (x t) *
          delayLogRatio xs (N.reaction r).source (x t)) := by
    simp only [delayField, Finset.sum_mul, delayLogRatio, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [e1, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [hg, delayIntegrand]
  ring

/-- `a (log b − log a + 1) ≤ b` for `a, b > 0`. -/
theorem mul_log_sub_log_add_one_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    a * (Real.log b - Real.log a + 1) ≤ b := by
  have h := Real.log_le_sub_one_of_pos (div_pos hb ha)
  rw [Real.log_div hb.ne' ha.ne'] at h
  have : a * (Real.log b - Real.log a) ≤ a * (b / a - 1) := mul_le_mul_of_nonneg_left h ha.le
  have he : a * (b / a - 1) = b - a := by field_simp
  rw [he] at this
  linarith

/-- **The derivative is nonpositive.** -/
theorem delayLyapunov_deriv_nonpos (N : Network S) (κ : RateConstants N) (τ : N.R → ℝ)
    {xs : Concentration S} (hxs : xs.Positive) (hcb : N.IsComplexBalanced κ xs)
    {x : ℝ → Concentration S} (hpos : ∀ t, (x t).Positive) (t : ℝ) :
    ∑ r, κ.k r * ((N.reaction r).source.massActionMonomial (x (t - τ r)) *
        (delayLogRatio xs (N.reaction r).target (x t) -
          delayLogRatio xs (N.reaction r).source (x (t - τ r)) + 1) -
      (N.reaction r).source.massActionMonomial (x t)) ≤ 0 := by
  set ms : N.R → ℝ := fun r => (N.reaction r).source.massActionMonomial xs with hms
  have hms0 : ∀ r, 0 < ms r := fun r => Complex.massActionMonomial_pos hxs _
  -- termwise bound
  have hterm : ∀ r, κ.k r * ((N.reaction r).source.massActionMonomial (x (t - τ r)) *
        (delayLogRatio xs (N.reaction r).target (x t) -
          delayLogRatio xs (N.reaction r).source (x (t - τ r)) + 1) -
      (N.reaction r).source.massActionMonomial (x t)) ≤
      κ.k r * ms r * (Real.exp (delayLogRatio xs (N.reaction r).target (x t)) -
        Real.exp (delayLogRatio xs (N.reaction r).source (x t))) := by
    intro r
    set A := (N.reaction r).source.massActionMonomial (x (t - τ r)) with hA
    have hA0 : 0 < A := Complex.massActionMonomial_pos (hpos _) _
    have hAe : A = ms r * Real.exp (delayLogRatio xs (N.reaction r).source (x (t - τ r))) :=
      massActionMonomial_eq_mul_exp_logRatio hxs (hpos _) _
    set B := ms r * Real.exp (delayLogRatio xs (N.reaction r).target (x t)) with hB
    have hB0 : 0 < B := mul_pos (hms0 r) (Real.exp_pos _)
    have hlogA : Real.log A = Real.log (ms r) + delayLogRatio xs (N.reaction r).source (x (t - τ r)) := by
      rw [hAe, Real.log_mul (hms0 r).ne' (Real.exp_pos _).ne', Real.log_exp]
    have hlogB : Real.log B = Real.log (ms r) + delayLogRatio xs (N.reaction r).target (x t) := by
      rw [hB, Real.log_mul (hms0 r).ne' (Real.exp_pos _).ne', Real.log_exp]
    have key := mul_log_sub_log_add_one_le hA0 hB0
    rw [hlogA, hlogB] at key
    have hmt : (N.reaction r).source.massActionMonomial (x t) =
        ms r * Real.exp (delayLogRatio xs (N.reaction r).source (x t)) :=
      massActionMonomial_eq_mul_exp_logRatio hxs (hpos _) _
    rw [hmt]
    have hk := (κ.positive r).le
    have : A * (delayLogRatio xs (N.reaction r).target (x t) -
        delayLogRatio xs (N.reaction r).source (x (t - τ r)) + 1) ≤ B := by linarith
    nlinarith
  refine (Finset.sum_le_sum fun r _ => hterm r).trans (le_of_eq ?_)
  -- complex balance at `x*`
  have hker := (N.isComplexBalanced_iff_kineticMap κ xs).mp hcb
  have hpair := N.sum_kineticMap_mul κ (N.complexMonomialVector xs)
    (fun c => Real.exp (delayLogRatio xs c.val (x t)))
  rw [hker] at hpair
  simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero] at hpair
  rw [hpair]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp [hms, sourceIdx, targetIdx]

/-- **Lipták–Hangos–Pituk–Szederkényi: the functional is nonincreasing** along every positive
solution of a delay mass-action system with a positive complex-balanced equilibrium. -/
theorem delayLyapunov_antitone (N : Network S) (κ : RateConstants N) (τ : N.R → ℝ)
    {xs : Concentration S} (hxs : xs.Positive) (hcb : N.IsComplexBalanced κ xs)
    {x : ℝ → Concentration S} (hx : N.IsDelaySolution κ τ x) (hpos : ∀ t, (x t).Positive) :
    Antitone (N.delayLyapunov κ τ xs x) :=
  antitone_of_hasDerivAt_nonpos (fun t => N.delayLyapunov_hasDerivAt κ τ (xs := xs) hx hpos t)
    (fun t => N.delayLyapunov_deriv_nonpos κ τ hxs hcb hpos t)

end Network

end CRNT
