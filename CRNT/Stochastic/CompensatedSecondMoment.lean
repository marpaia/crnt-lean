import CRNT.Stochastic.MinimalSemigroupDynkin
import CRNT.Stochastic.MinimalSemigroupNetwork
import CRNT.Stochastic.FluctuationSecondMoment

/-!
# The compensated second moment of the jump system

This module supplies the **second-moment** half of the Dynkin machinery that leaf **P9**
(central limit theorem; diffusion approximation) of `docs/field-map.md` is missing, namely the
Meyn–Tweedie second-moment estimate for a Markov chain (W. Meyn and D. Tweedie, *Markov Chains
and Stochastic Stability*, 2nd ed., Ch. 1 §1.3; 3rd ed., Ch. 13), the ingredient that turns a
Foster–Lyapunov condition into a fluctuation-scale (`O(√t)`) bound on the chain.

## The two ingredients

* The **Dynkin formula** in the path-free form of this repository: if `Q V ≤ −f + K` with
  `V, f ≥ 0` and `K ≥ 0`, then for every `T ≥ 0`
  `∫₀ᵀ ∑_b P(t)(a, b) f(b) dt ≤ V(a) + K T` (`CRNT.JumpSystem.dynkin_le`, the `k`-jump
  version, and `CRNT.JumpSystem.integral_sum_Pmin_mul_le`, the minimal-transition-function
  version). This is the *first-moment* machinery: it bounds the time integral of a **deficit**
  `f`.
* The **second-moment estimate** proved here: the drift of the square of a bounded observable is
  controlled by the drift of the observable and by the exit rate,
  `Q(V²)(a) ≤ 2 M K + M² q(a)` when `0 ≤ V ≤ M` and `Q V ≤ K`
  (`CRNT.JumpSystem.drift_sq_le`), whence the *compensated* second-moment Dynkin inequality
  (`CRNT.JumpSystem.dynkin_sq_le`, `CRNT.JumpSystem.dynkin_sq_le_k`,
  `CRNT.JumpSystem.sum_Pmin_mul_sq_le`).

The two fit together exactly as in Meyn–Tweedie: the first-moment estimate controls the
*mean* of an observable along the chain, and the second-moment estimate controls the
*fluctuation* around it. This is the path-free counterpart of the second moment of the
deterministic-time-change Poisson fluctuation computed in the campaign module
`CRNT/Stochastic/FluctuationSecondMoment.lean`
(`CRNT.Stochastic.secondMoment_aggregate_scaledClock`,
`CRNT.Stochastic.secondMoment_centered_aggregate_scaledClock`,
`CRNT.Stochastic.fluctScale_meas_aggregate_scaledClock_ge_le`): there the second moment of the
Poisson fluctuation is computed algebraically from independence, here the second moment of the
*jump system* is computed from the drift of the observable. Both are the `O(1)`-fluctuation-scale
ingredients that leaf P9 asks for.

## What is proved

* `drift_sq_le`: the second-moment drift bound `Q(V²)(a) ≤ 2 M K + M² q(a)` for a bounded
  Lyapunov function `0 ≤ V ≤ M` with `Q V ≤ K`. This is the algebraic core: the increment
  `(V(next) − V(a))²` is bounded by `M²` because `|V(next) − V(a)| ≤ M`, and the first-order
  term `2 V(a) (V(next) − V(a))` is bounded by `2 M (V(next) − V(a))`.
* `drift_sq_sub`: the compensation identity `Q((V − c)²)(a) = Q(V²)(a) − 2 c Q V(a)` — a constant
  shift of the observable changes the first-order term of the drift only.
* `dynkin_sq_le_k`: the Dynkin inequality for the square of an observable, in the same `k`-jump
  form as `CRNT.JumpSystem.dynkin_le`.
* `dynkin_sq_le`: the Dynkin inequality for the square of an observable in the minimal
  transition function, in the *deficit* form: if `Q(V²) ≤ −f + K`, then
  `∫₀ᵀ ∑_b Pmin(t)(a, b) f(b) dt ≤ V(a)² + K T`. Taking `f = V²` (`dynkin_sq_le_self`) gives the
  "the second moment is bounded by the initial second moment plus the deficit times the time"
  statement — the exact shape of the second-moment Dynkin inequality of Meyn–Tweedie.
* `sum_Pmin_mul_le_of_const_drift`: the terminal form of the Dynkin inequality for a
  nonnegative observable whose drift is bounded by a constant: `∑_b Pmin(T)(a, b) W(b) ≤ W(a) + C T`.
* `sum_Pmin_mul_sq_le`: the terminal (fixed-time) second-moment estimate
  `∑_b Pmin(T)(a, b) V(b)² ≤ V(a)² + C T` under the hypothesis `Q(V²) ≤ C`; this is the
  **unbounded** version — no bound on `V` is needed, only a bound on the drift of its square.
* `sum_Pmin_mul_sq_le_bounded`: the same estimate for a bounded `V` with `Q V ≤ K` and a
  uniform bound `q ≤ Q` on the exit rate; the constant is `2 M K + M² Q`.
* `integral_sum_Pmin_mul_sq_le`: the time-integrated version of the second-moment estimate,
  `∫₀ᵀ ∑_b Pmin(t)(a, b) V(b)² dt ≤ V(a)² T + (2 M K + M² Q) T² / 2`.
* `fluctuation_sq_le`, `fluctuation_sq_le_lower`, `fluctuation_chebyshev`: the
  fluctuation-scale consequences: the deviation `V(b) − V(a)` of the observable from its initial
  value has second moment growing at most linearly in `T`, and the corresponding Chebyshev
  (tail) bound. These are the path-free analogues of
  `CRNT.Stochastic.fluctScale_meas_aggregate_scaledClock_ge_le`.
* `Network.jumpSystem_drift_observableGenerator`: the drift of an observable under the jump
  system of stochastic mass-action kinetics is the backward generator of the observable
  (`CRNT.Network.observableGenerator` of `CRNT/Stochastic/FosterLyapunov.lean`), so the results
  below apply to the CRN chains themselves.
* `JumpSystem.secondMoment_indTrue`: a concrete instance, the two-state system `false → true`
  at rate `lam` with the observable `1_{true}`.

## A remark on the shape of the second-moment Dynkin inequality

The second-moment Dynkin inequality of Meyn–Tweedie comes in two shapes, and the repository's
machinery supports both of them:

* the **integral** shape, `∫₀ᵀ ∑_b Pmin(t)(a, b) f(b) dt ≤ V(a)² + K T`, which needs a *deficit*
  `f ≥ 0` with `Q(V²) ≤ −f + K` (`dynkin_sq_le`, and `dynkin_sq_le_self` for `f = V²`);
* the **terminal** shape, `∑_b Pmin(T)(a, b) V(b)² ≤ V(a)² + C T`, which needs a bound `C` on the
  drift of `V²` alone (`sum_Pmin_mul_sq_le`).

The two hypotheses are *not* interchangeable. The drift bound of `drift_sq_le`,
`Q(V²)(a) ≤ 2 M K + M² q(a)`, depends on the state through the exit rate `q(a)`, so it cannot be
used as the uniform constant of a Dynkin inequality; it becomes one only after the exit rate is
bounded uniformly (`sum_Pmin_mul_sq_le_bounded`, with the constant `2 M K + M² Q`). Conversely a
statement of the shape `∫₀ᵀ ∑_b Pmin(t)(a, b) V(b)² dt ≤ V(a)² + (2 M K + M² q(a)) T` is *false*
in general (take `V ≡ 1` at a state with `q(a) = 0`: the left-hand side is `T` and the
right-hand side is `1`); the correct integral statement is the one of `dynkin_sq_le_self` (with
the dissipativity hypothesis on `V²`) or the `T²`-scaled one of
`integral_sum_Pmin_mul_sq_le`.

## What remains open

The **path-space** statement of leaf P9 — the event "the chain leaves `B_i` in the `i`-th
window", identified with the exit mass (`CRNT.JumpSystem.exitMass`,
`CRNT.JumpSystem.exitMass_eq_tsum_Pexit`), and the uniform-in-time bound on the running
supremum of the fluctuation — is *not* proved here and cannot be: the library has no i.i.d.
exponential measure, hence no exponential martingale, and no strong Markov property, hence no
optional stopping. Everything in this module is therefore stated for the **path-free**
quantities: the minimal transition function `Pmin`, the exit mass
(`CRNT.JumpSystem.exitMass`) and the `f`-norm bounds built on them. The fluctuation-scale
estimate proved here is therefore a *fixed-time* (and time-integrated) statement about `Pmin`,
not a statement about sample paths.

The unbounded second-moment estimate of Meyn–Tweedie is available in the form
`sum_Pmin_mul_sq_le` under the hypothesis that the drift of `V²` is bounded; the classical
hypothesis "there is a bounded `V` with `Q V ≤ K` and `Q(V²) ≤ C`" is exactly the bounded
version `sum_Pmin_mul_sq_le_bounded` (with `C = 2 M K + M² Q`).
-/

open MeasureTheory intervalIntegral Set Filter
open scoped BigOperators Topology

namespace CRNT

namespace JumpSystem

variable {α : Type*} [DecidableEq α] (J : JumpSystem α)

set_option maxHeartbeats 800000

/-! ## The second-order scalar estimate -/

/-- **The scalar second-order estimate.** If `0 ≤ M` and `0 ≤ w ≤ M`, then for every `v`,
`w ^ 2 - v ^ 2 ≤ 2 * M * (w - v) + M ^ 2`.

Indeed `w ^ 2 - v ^ 2 - 2 * M * (w - v) = (w - M) ^ 2 - (v - M) ^ 2 ≤ M ^ 2`, because
`|w - M| ≤ M`. This is the elementary form of "the second-order term is bounded by the square
of the bound of the observable, and the first-order term by twice the bound times the
increment". -/
theorem sq_sub_sq_le_two_mul_sub_add_sq {M w : ℝ} (hM : 0 ≤ M) (hw0 : 0 ≤ w) (hwM : w ≤ M)
    (v : ℝ) :
    w ^ 2 - v ^ 2 ≤ 2 * M * (w - v) + M ^ 2 := by
  have h1 : (w - M) ^ 2 ≤ M ^ 2 := by
    have habs : |w - M| ≤ M := (abs_le).mpr ⟨by linarith, by linarith⟩
    have hsq : (w - M) ^ 2 ≤ M ^ 2 := (sq_le_sq).2 (by simpa [abs_of_nonneg hM] using habs)
    exact hsq
  have h2 : 0 ≤ (v - M) ^ 2 := sq_nonneg _
  have h3 : w ^ 2 - v ^ 2 - 2 * M * (w - v) = (w - M) ^ 2 - (v - M) ^ 2 := by ring
  linarith [h1, h2, h3]

/-! ## The second-moment drift bound -/

omit [DecidableEq α] in
/-- **The second-moment drift of a bounded Lyapunov function.**  If `0 ≤ V ≤ M` on the state
space and the drift of `V` is bounded by `K`, then the drift of `V²` is bounded by
`2 M K + M² · q` (where `q` is the total exit rate): the first-order term is `2 V QV` and the
second-order term is `E[(ΔV)²] ≤ M² q` because `|ΔV| ≤ M`.

This is the Meyn–Tweedie second-moment estimate at the level of the generator; it is the
hypothesis of the compensated second-moment Dynkin inequality below. -/
theorem drift_sq_le (V : α → ℝ) {M K : ℝ}
    (hV : ∀ a, 0 ≤ V a) (hV' : ∀ a, V a ≤ M)
    (hK : ∀ a, J.drift V a ≤ K) (hM : 0 ≤ M) :
    ∀ a, J.drift (fun b => V b ^ 2) a ≤ 2 * M * K + M ^ 2 * J.q a := by
  intro a
  have hq : (∑ i, J.rate i a) = J.q a := rfl
  have hsum : (∑ i, J.rate i a * (V (J.next i a) - V a)) = J.drift V a := by
    calc (∑ i, J.rate i a * (V (J.next i a) - V a))
        = ∑ i, (J.rate i a * V (J.next i a) - J.rate i a * V a) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
      _ = (∑ i, J.rate i a * V (J.next i a)) - ∑ i, J.rate i a * V a := by
          exact Finset.sum_sub_distrib _ _
      _ = (J.drift V a + J.q a * V a) - V a * J.q a := by
          rw [J.sum_rate_mul_next, ← Finset.sum_mul, hq]
          ring
      _ = J.drift V a := by ring
  calc J.drift (fun b => V b ^ 2) a
      = ∑ i, J.rate i a * ((V (J.next i a)) ^ 2 - (V a) ^ 2) := by
        simp only [drift]
    _ ≤ ∑ i, J.rate i a * (2 * M * (V (J.next i a) - V a) + M ^ 2) := by
        refine Finset.sum_le_sum fun i _ => ?_
        exact mul_le_mul_of_nonneg_left
          (sq_sub_sq_le_two_mul_sub_add_sq hM (hV (J.next i a)) (hV' (J.next i a)) (V a))
          (J.rate_nonneg i a)
    _ = 2 * M * J.drift V a + M ^ 2 * J.q a := by
        have h2 : (∑ i, J.rate i a * M ^ 2) = M ^ 2 * J.q a := by
          rw [← Finset.sum_mul, hq]
          ring
        have h3 : (∑ i, J.rate i a * (2 * M * (V (J.next i a) - V a))) = 2 * M * J.drift V a := by
          have h4 : (∑ i, J.rate i a * (2 * M * (V (J.next i a) - V a)))
              = 2 * M * (∑ i, J.rate i a * (V (J.next i a) - V a)) := by
            calc (∑ i, J.rate i a * (2 * M * (V (J.next i a) - V a)))
                = ∑ i, 2 * M * (J.rate i a * (V (J.next i a) - V a)) := by
                  apply Finset.sum_congr rfl
                  intro i _
                  ring
              _ = 2 * M * (∑ i, J.rate i a * (V (J.next i a) - V a)) := by
                rw [← Finset.mul_sum]
          rw [h4, hsum]
        calc (∑ i, J.rate i a * (2 * M * (V (J.next i a) - V a) + M ^ 2))
            = ∑ i, (J.rate i a * (2 * M * (V (J.next i a) - V a)) + J.rate i a * M ^ 2) := by
              apply Finset.sum_congr rfl
              intro i _
              ring
          _ = (∑ i, J.rate i a * (2 * M * (V (J.next i a) - V a))) + ∑ i, J.rate i a * M ^ 2 :=
            Finset.sum_add_distrib
          _ = 2 * M * J.drift V a + M ^ 2 * J.q a := by rw [h3, h2]
    _ ≤ 2 * M * K + M ^ 2 * J.q a := by
        have h := mul_le_mul_of_nonneg_left (hK a) hM
        linarith

omit [DecidableEq α] in
/-- **The drift of a shifted square.** For any constant `c`,
`Q((V - c)²)(a) = Q(V²)(a) - 2 c Q V(a)`: a constant shift of the observable changes the
first-order term only. This is the "compensation" of the second-moment drift. -/
theorem drift_sq_sub (V : α → ℝ) (c : ℝ) (a : α) :
    J.drift (fun b => (V b - c) ^ 2) a = J.drift (fun b => V b ^ 2) a - 2 * c * J.drift V a := by
  have hq : (∑ i, J.rate i a) = J.q a := rfl
  have h1 : (∑ i, J.rate i a * (V (J.next i a) - V a)) = J.drift V a := by
    calc (∑ i, J.rate i a * (V (J.next i a) - V a))
        = ∑ i, (J.rate i a * V (J.next i a) - J.rate i a * V a) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
      _ = (∑ i, J.rate i a * V (J.next i a)) - ∑ i, J.rate i a * V a := by
          exact Finset.sum_sub_distrib _ _
      _ = (J.drift V a + J.q a * V a) - V a * J.q a := by
          rw [J.sum_rate_mul_next, ← Finset.sum_mul, hq]
          ring
      _ = J.drift V a := by ring
  have h2 : (∑ i, J.rate i a * ((V (J.next i a) - c) ^ 2 - (V a - c) ^ 2))
      = (∑ i, J.rate i a * ((V (J.next i a)) ^ 2 - (V a) ^ 2)) - 2 * c * (∑ i,
        J.rate i a * (V (J.next i a) - V a)) := by
    calc (∑ i, J.rate i a * ((V (J.next i a) - c) ^ 2 - (V a - c) ^ 2))
        = ∑ i, (J.rate i a * ((V (J.next i a)) ^ 2 - (V a) ^ 2) -
            2 * c * (J.rate i a * (V (J.next i a) - V a))) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
      _ = (∑ i, J.rate i a * ((V (J.next i a)) ^ 2 - (V a) ^ 2)) -
            ∑ i, 2 * c * (J.rate i a * (V (J.next i a) - V a)) := by
          exact Finset.sum_sub_distrib _ _
      _ = (∑ i, J.rate i a * ((V (J.next i a)) ^ 2 - (V a) ^ 2)) -
            2 * c * (∑ i, J.rate i a * (V (J.next i a) - V a)) := by
          rw [← Finset.mul_sum]
  have h3 : (∑ i, J.rate i a * ((V (J.next i a)) ^ 2 - (V a) ^ 2))
      = J.drift (fun b => V b ^ 2) a := by
        simp only [drift]
  have h0 : J.drift (fun b => (V b - c) ^ 2) a
      = ∑ i, J.rate i a * ((V (J.next i a) - c) ^ 2 - (V a - c) ^ 2) := by
        simp only [drift]
  rw [h0, h2, h3, h1]

/-! ## The compensated second-moment Dynkin inequality -/

/-- **The Dynkin inequality for the square of an observable, with `k` jumps.** This is
`CRNT.JumpSystem.dynkin_le` applied to the observable `V²`: if `Q(V²) ≤ −f + K` with `f ≥ 0`
and `K ≥ 0`, then the time integral of the weighted row mass of the deficit `f` plus the
weighted row mass of `V²` at time `T` is at most `V(a)² + K T`. -/
theorem dynkin_sq_le_k (V : α → ℝ) {f : α → ℝ} {K' : ℝ} (hK' : 0 ≤ K')
    (hdrift : ∀ a, J.drift (fun b => V b ^ 2) a ≤ -f a + K') (k : ℕ) :
    ∀ T, 0 ≤ T → ∀ a,
      (∫ t in (0 : ℝ)..T, J.wmass f k t a) + J.wmass (fun b => V b ^ 2) k T a
        ≤ (V a) ^ 2 + K' * T := by
  intro T hT a
  exact J.dynkin_le (fun b => V b ^ 2) f (fun b => sq_nonneg (V b)) hK' hdrift k T hT a

/-- **The compensated second-moment Dynkin inequality.** If `Q(V²) ≤ −f + K` with `f ≥ 0` and
`K ≥ 0`, then the time integral of the second moment of the transition probabilities is bounded
by the initial second moment plus the deficit bound times the time:

  `∫₀ᵀ ∑_b Pmin(t)(a, b) f(b) dt ≤ V(a)² + K T`.

This is `CRNT.JumpSystem.integral_sum_Pmin_mul_le` applied to the observable `V²`; it is the
path-free form of the Dynkin formula for the second moment. -/
theorem dynkin_sq_le (V : α → ℝ) {f : α → ℝ} {K : ℝ} (hf : ∀ a, 0 ≤ f a)
    (hK : 0 ≤ K) (hdrift : ∀ a, J.drift (fun b => V b ^ 2) a ≤ -f a + K)
    {T : ℝ} (hT : 0 ≤ T) (a : α) (F : Finset α) :
    ∫ t in (0 : ℝ)..T, ∑ b ∈ F, J.Pmin t a b * f b ≤ (V a) ^ 2 + K * T := by
  exact J.integral_sum_Pmin_mul_le (fun b => V b ^ 2) f (fun b => sq_nonneg (V b)) hf hK
    (fun b => by simpa using hdrift b) hT a F

/-- **The second moment bounded by the initial second moment plus the deficit times the time.**
If the drift of the square of the observable is bounded by `−V² + K` (a strict Lyapunov
condition for the second moment), then

  `∫₀ᵀ ∑_b Pmin(t)(a, b) V(b)² dt ≤ V(a)² + K T`.

This is the special case `f = V²` of `dynkin_sq_le`. -/
theorem dynkin_sq_le_self (V : α → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hdrift : ∀ a, J.drift (fun b => V b ^ 2) a ≤ -(V a) ^ 2 + K)
    {T : ℝ} (hT : 0 ≤ T) (a : α) (F : Finset α) :
    ∫ t in (0 : ℝ)..T, ∑ b ∈ F, J.Pmin t a b * (V b) ^ 2 ≤ (V a) ^ 2 + K * T := by
  exact J.dynkin_sq_le V (fun b => sq_nonneg (V b)) hK
    (fun b => by simpa using hdrift b) hT a F

/-- **The terminal form of the Dynkin inequality for a nonnegative observable.** If `W ≥ 0` and
the drift of `W` is bounded by a constant `C ≥ 0`, then the weighted row mass of `W` for the
minimal transition function at time `T` is at most `W(a) + C T`:

  `∑_b Pmin(T)(a, b) W(b) ≤ W(a) + C T`.

This is `CRNT.JumpSystem.dynkin_le` with the deficit `f = 0`, followed by the limit over the
number of jumps. -/
theorem sum_Pmin_mul_le_of_const_drift (W : α → ℝ) {C : ℝ} (hW : ∀ a, 0 ≤ W a) (hC : 0 ≤ C)
    (hdrift : ∀ a, J.drift W a ≤ C) {T : ℝ} (hT : 0 ≤ T) (a : α) (F : Finset α) :
    ∑ b ∈ F, J.Pmin T a b * W b ≤ W a + C * T := by
  have hk : ∀ k, ∑ b ∈ F, J.P k T a b * W b ≤ W a + C * T := by
    intro k
    have h := J.dynkin_le W (fun _ => (0 : ℝ)) hW hC (fun b => by simpa using hdrift b)
      k T hT a
    have hz : (∫ t in (0 : ℝ)..T, J.wmass (fun _ => (0 : ℝ)) k t a) = 0 := by
      have hw : J.wmass (fun _ => (0 : ℝ)) k = fun t a => 0 := by
        funext t
        funext a
        unfold wmass
        simp
      rw [hw]
      simp
    rw [hz] at h
    have h' : J.wmass W k T a ≤ W a + C * T := by
      simpa only [zero_add] using h
    calc (∑ b ∈ F, J.P k T a b * W b)
        ≤ ∑ b ∈ F ∪ J.reachK k a, J.P k T a b * W b :=
          Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left fun b _ _ =>
            mul_nonneg (J.P_nonneg k T hT a b) (hW b)
      _ = J.wmass W k T a := J.sum_P_mul_eq_wmass_of_subset _ k T a Finset.subset_union_right
      _ ≤ W a + C * T := h'
  have hlim : Tendsto (fun k => ∑ b ∈ F, J.P k T a b * W b) atTop
      (𝓝 (∑ b ∈ F, J.Pmin T a b * W b)) :=
    tendsto_finsetSum _ fun b _ => (J.tendsto_P T hT a b).mul_const _
  exact le_of_tendsto' hlim hk

/-- **The second-moment estimate for the minimal transition function (unbounded version).** If
the drift of the square of the observable is bounded by a constant `C ≥ 0`, then the second
moment of the transition probabilities at time `T` is at most the initial second moment plus
`C T`:

  `∑_b Pmin(T)(a, b) V(b)² ≤ V(a)² + C T`.

No bound on `V` itself is needed: this is the Meyn–Tweedie second-moment condition with the
hypothesis "the drift of `V²` is bounded". -/
theorem sum_Pmin_mul_sq_le (V : α → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hdrift : ∀ a, J.drift (fun b => V b ^ 2) a ≤ C) {T : ℝ} (hT : 0 ≤ T) (a : α)
    (F : Finset α) :
    ∑ b ∈ F, J.Pmin T a b * (V b) ^ 2 ≤ (V a) ^ 2 + C * T := by
  exact J.sum_Pmin_mul_le_of_const_drift (fun b => V b ^ 2) (fun b => sq_nonneg (V b)) hC hdrift hT a F

/-- **The second-moment estimate for a bounded Lyapunov function.** If `0 ≤ V ≤ M` and the drift
of `V` is bounded by `K ≥ 0`, and the exit rate is bounded by `Q ≥ 0`, then the second moment of
the transition probabilities at time `T` is at most the initial second moment plus
`(2 M K + M² Q) T`. The constant `2 M K + M² Q` is the Meyn–Tweedie second-moment bound
`2 M K + M² q` with the exit rate replaced by its uniform bound. -/
theorem sum_Pmin_mul_sq_le_bounded (V : α → ℝ) {M K Q : ℝ}
    (hV : ∀ a, 0 ≤ V a) (hV' : ∀ a, V a ≤ M) (hK : ∀ a, J.drift V a ≤ K) (hM : 0 ≤ M)
    (hK0 : 0 ≤ K) (hQ : ∀ a, J.q a ≤ Q) (hQ0 : 0 ≤ Q)
    {T : ℝ} (hT : 0 ≤ T) (a : α) (F : Finset α) :
    ∑ b ∈ F, J.Pmin T a b * (V b) ^ 2 ≤ (V a) ^ 2 + (2 * M * K + M ^ 2 * Q) * T := by
  have hC : 0 ≤ 2 * M * K + M ^ 2 * Q := by positivity
  refine J.sum_Pmin_mul_sq_le V hC ?_ hT a F
  intro b
  have h1 := J.drift_sq_le V hV hV' hK hM b
  have h2 := mul_le_mul_of_nonneg_left (hQ b) (sq_nonneg M)
  linarith

/-- `∫₀ᵀ t dt = T² / 2`. -/
theorem integral_id_zero (T : ℝ) : ∫ t in (0 : ℝ)..T, t = T ^ 2 / 2 := by
  have hd : ∀ s ∈ uIcc (0 : ℝ) T, HasDerivAt (fun x : ℝ => x ^ 2 / 2) s s := by
    intro s _
    have h2 := ((hasDerivAt_id s).pow 2).div_const 2
    convert h2 using 1 <;> simp_all
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (by apply Continuous.intervalIntegrable; fun_prop)]
  simp

/-- **The time-integrated second-moment estimate.** Under the hypotheses of
`sum_Pmin_mul_sq_le_bounded`, the time integral of the second moment of the transition
probabilities is at most the initial second moment times the time plus the second-moment bound
times `T² / 2`:

  `∫₀ᵀ ∑_b Pmin(t)(a, b) V(b)² dt ≤ V(a)² T + (2 M K + M² Q) T² / 2`.

This is the integrated form of the Dynkin formula for the second moment. -/
theorem integral_sum_Pmin_mul_sq_le (V : α → ℝ) {M K Q : ℝ}
    (hV : ∀ a, 0 ≤ V a) (hV' : ∀ a, V a ≤ M) (hK : ∀ a, J.drift V a ≤ K) (hM : 0 ≤ M)
    (hK0 : 0 ≤ K) (hQ : ∀ a, J.q a ≤ Q) (hQ0 : 0 ≤ Q)
    {T : ℝ} (hT : 0 ≤ T) (a : α) (F : Finset α) :
    ∫ t in (0 : ℝ)..T, ∑ b ∈ F, J.Pmin t a b * (V b) ^ 2
      ≤ (V a) ^ 2 * T + (2 * M * K + M ^ 2 * Q) * T ^ 2 / 2 := by
  have hpoint : ∀ t ∈ Icc (0 : ℝ) T,
      ∑ b ∈ F, J.Pmin t a b * (V b) ^ 2 ≤ (V a) ^ 2 + (2 * M * K + M ^ 2 * Q) * t := by
    intro t ht
    exact J.sum_Pmin_mul_sq_le_bounded V hV hV' hK hM hK0 hQ hQ0 ht.1 a F
  have hmono := intervalIntegral.integral_mono_on (μ := volume) hT
    ((continuousOn_finsetSum _ fun b _ =>
      (J.continuousOn_Pmin a b).mul continuousOn_const).mono
        (by rw [uIcc_of_le hT]; exact Icc_subset_Ici_self)).intervalIntegrable
    (by apply Continuous.intervalIntegrable; fun_prop)
    (fun t ht => hpoint t ht)
  have hint : (∫ t in (0 : ℝ)..T, ((V a) ^ 2 + (2 * M * K + M ^ 2 * Q) * t))
      = (V a) ^ 2 * T + (2 * M * K + M ^ 2 * Q) * (T ^ 2 / 2) := by
    calc (∫ t in (0 : ℝ)..T, ((V a) ^ 2 + (2 * M * K + M ^ 2 * Q) * t))
        = (∫ t in (0 : ℝ)..T, (V a) ^ 2) +
            ∫ t in (0 : ℝ)..T, (2 * M * K + M ^ 2 * Q) * t :=
          intervalIntegral.integral_add (μ := volume)
            (by apply Continuous.intervalIntegrable; fun_prop)
            (by apply Continuous.intervalIntegrable; fun_prop)
      _ = (V a) ^ 2 * T + (2 * M * K + M ^ 2 * Q) * (T ^ 2 / 2) := by
          rw [intervalIntegral.integral_const]
          rw [show (fun t => (2 * M * K + M ^ 2 * Q) * t)
              = fun t => t * (2 * M * K + M ^ 2 * Q) from funext fun t => mul_comm _ _]
          rw [intervalIntegral.integral_mul_const, integral_id_zero]
          ring
  calc (∫ t in (0 : ℝ)..T, ∑ b ∈ F, J.Pmin t a b * (V b) ^ 2)
      ≤ ∫ t in (0 : ℝ)..T, ((V a) ^ 2 + (2 * M * K + M ^ 2 * Q) * t) := hmono
    _ = (V a) ^ 2 * T + (2 * M * K + M ^ 2 * Q) * T ^ 2 / 2 := by
        rw [hint]
        ring

/-! ## The fluctuation scale -/

/-- **The fluctuation scale of a bounded observable.** The deviation `V(b) − V(a)` of the
observable from its initial value has second moment growing at most linearly in the time:

  `∑_b Pmin(T)(a, b) (V(b) − V(a))² ≤ 2 V(a)² + (2 M K + M² Q) T`.

Hence the fluctuation is at the `O(√T)` scale, uniformly in the starting state. -/
theorem fluctuation_sq_le (V : α → ℝ) {M K Q : ℝ}
    (hV : ∀ a, 0 ≤ V a) (hV' : ∀ a, V a ≤ M) (hK : ∀ a, J.drift V a ≤ K) (hM : 0 ≤ M)
    (hK0 : 0 ≤ K) (hQ : ∀ a, J.q a ≤ Q) (hQ0 : 0 ≤ Q)
    {T : ℝ} (hT : 0 ≤ T) (a : α) (F : Finset α) :
    ∑ b ∈ F, J.Pmin T a b * (V b - V a) ^ 2 ≤ 2 * (V a) ^ 2 + (2 * M * K + M ^ 2 * Q) * T := by
  have h1 := J.sum_Pmin_mul_sq_le_bounded V hV hV' hK hM hK0 hQ hQ0 hT a F
  have h2 : ∑ b ∈ F, J.Pmin T a b ≤ 1 := J.sum_Pmin_le_one T hT a F
  have hsq : ∀ b : α, (V b - V a) ^ 2 ≤ (V b) ^ 2 + (V a) ^ 2 := by
    intro b
    have htwo : (0 : ℝ) ≤ 2 := by norm_num
    have hpa : 0 ≤ 2 * V a := mul_nonneg htwo (hV a)
    have hpos : 0 ≤ (2 * V a) * V b := mul_nonneg hpa (hV b)
    nlinarith [sq_nonneg (V b - V a)]
  calc (∑ b ∈ F, J.Pmin T a b * (V b - V a) ^ 2)
      ≤ ∑ b ∈ F, J.Pmin T a b * ((V b) ^ 2 + (V a) ^ 2) := by
        refine Finset.sum_le_sum fun b _ => ?_
        exact mul_le_mul_of_nonneg_left (hsq b) (J.Pmin_nonneg T hT a b)
    _ = (∑ b ∈ F, J.Pmin T a b * (V b) ^ 2) + (V a) ^ 2 * (∑ b ∈ F, J.Pmin T a b) := by
        have h3 : (∑ b ∈ F, J.Pmin T a b * ((V b) ^ 2 + (V a) ^ 2))
            = (∑ b ∈ F, J.Pmin T a b * (V b) ^ 2) + ∑ b ∈ F, J.Pmin T a b * (V a) ^ 2 := by
          calc (∑ b ∈ F, J.Pmin T a b * ((V b) ^ 2 + (V a) ^ 2))
              = ∑ b ∈ F, (J.Pmin T a b * (V b) ^ 2 + J.Pmin T a b * (V a) ^ 2) := by
                apply Finset.sum_congr rfl
                intro b _
                ring
            _ = (∑ b ∈ F, J.Pmin T a b * (V b) ^ 2) + ∑ b ∈ F, J.Pmin T a b * (V a) ^ 2 :=
              Finset.sum_add_distrib
        have h4 : (∑ b ∈ F, J.Pmin T a b * (V a) ^ 2) = (V a) ^ 2 * ∑ b ∈ F, J.Pmin T a b := by
          rw [← Finset.sum_mul]
          ring
        rw [h3, h4]
    _ ≤ _ := by
        have h4 := mul_le_mul_of_nonneg_left h2 (sq_nonneg (V a))
        linarith

/-- **The fluctuation scale with a lower bound on the drift.** If in addition the drift of `V`
is bounded below by `−L`, the deviation `V(b) − V(a)` satisfies the sharper bound

  `∑_b Pmin(T)(a, b) (V(b) − V(a))² ≤ (2 M K + M² Q + 2 L V(a)) T`.

The proof uses the compensation identity `drift_sq_sub`: the shift by the initial value `V(a)`
only changes the first-order term of the drift. -/
theorem fluctuation_sq_le_lower (V : α → ℝ) {M K Q L : ℝ}
    (hV : ∀ a, 0 ≤ V a) (hV' : ∀ a, V a ≤ M) (hK : ∀ a, J.drift V a ≤ K) (hM : 0 ≤ M)
    (hK0 : 0 ≤ K) (hKL : ∀ a, -L ≤ J.drift V a) (hL0 : 0 ≤ L) (hQ : ∀ a, J.q a ≤ Q)
    (hQ0 : 0 ≤ Q)
    {T : ℝ} (hT : 0 ≤ T) (a : α) (F : Finset α) :
    ∑ b ∈ F, J.Pmin T a b * (V b - V a) ^ 2
      ≤ (2 * M * K + M ^ 2 * Q + 2 * V a * L) * T := by
  have hdrift : ∀ b : α, J.drift (fun c => (V c - V a) ^ 2) b
      ≤ 2 * M * K + M ^ 2 * Q + 2 * V a * L := by
    intro b
    rw [J.drift_sq_sub]
    have h1 := J.drift_sq_le V hV hV' hK hM b
    have h2 := mul_le_mul_of_nonneg_left (hQ b) (sq_nonneg M)
    have h3 : -2 * V a * J.drift V b ≤ 2 * V a * L := by
      have htwo : (0 : ℝ) ≤ 2 := by norm_num
      have hnonneg : 0 ≤ 2 * V a := mul_nonneg htwo (hV a)
      have hneg : 2 * V a * -L ≤ 2 * V a * J.drift V b :=
        mul_le_mul_of_nonneg_left (hKL b) hnonneg
      linarith
    linarith
  have hC : 0 ≤ 2 * M * K + M ^ 2 * Q + 2 * V a * L := by
    have htwo : (0 : ℝ) ≤ 2 := by norm_num
    have h1 : 0 ≤ 2 * M * K := mul_nonneg (mul_nonneg htwo hM) hK0
    have h2 : 0 ≤ M ^ 2 * Q := mul_nonneg (sq_nonneg M) hQ0
    have h3 : 0 ≤ 2 * V a * L := mul_nonneg (mul_nonneg htwo (hV a)) hL0
    linarith
  have h1 := J.sum_Pmin_mul_le_of_const_drift (fun b => (V b - V a) ^ 2) (fun b => sq_nonneg (V b - V a))
    hC hdrift hT a F
  rw [show (V a - V a) ^ 2 = 0 by ring] at h1
  linarith

/-- **The Chebyshev bound for the fluctuation.** The probability that the observable deviates
from its initial value by at least `δ > 0` is at most the second moment divided by `δ²`:

  `∑_{b ∈ G} Pmin(T)(a, b) ≤ (2 V(a)² + (2 M K + M² Q) T) / δ²`

for every set `G` of states on which the deviation is at least `δ`. This is the path-free
analogue of `CRNT.Stochastic.fluctScale_meas_aggregate_scaledClock_ge_le`. -/
theorem fluctuation_chebyshev (V : α → ℝ) {M K Q : ℝ}
    (hV : ∀ a, 0 ≤ V a) (hV' : ∀ a, V a ≤ M) (hK : ∀ a, J.drift V a ≤ K) (hM : 0 ≤ M)
    (hK0 : 0 ≤ K) (hQ : ∀ a, J.q a ≤ Q) (hQ0 : 0 ≤ Q)
    {T : ℝ} (hT : 0 ≤ T) (a : α) (F : Finset α) {δ : ℝ} (hδ : 0 < δ) (G : Finset α)
    (hGF : G ⊆ F) (hG : ∀ b ∈ G, δ ≤ |V b - V a|) :
    ∑ b ∈ G, J.Pmin T a b ≤ (2 * (V a) ^ 2 + (2 * M * K + M ^ 2 * Q) * T) / δ ^ 2 := by
  have hsq : ∀ b ∈ G, δ ^ 2 ≤ (V b - V a) ^ 2 := by
    intro b hb
    have h1 : δ ^ 2 ≤ |V b - V a| ^ 2 :=
      (sq_le_sq).2 (by simpa [abs_of_pos hδ] using hG b hb)
    have h2 : |V b - V a| ^ 2 = (V b - V a) ^ 2 := sq_abs _
    linarith
  rw [le_div_iff₀ (sq_pos_of_pos hδ)]
  calc (∑ b ∈ G, J.Pmin T a b) * δ ^ 2
      = ∑ b ∈ G, J.Pmin T a b * δ ^ 2 := by
        rw [Finset.sum_mul]
    _ ≤ ∑ b ∈ G, J.Pmin T a b * (V b - V a) ^ 2 := by
        refine Finset.sum_le_sum fun b hb => ?_
        exact mul_le_mul_of_nonneg_left (hsq b hb) (J.Pmin_nonneg T hT a b)
    _ ≤ ∑ b ∈ F, J.Pmin T a b * (V b - V a) ^ 2 := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hGF fun b _ _ =>
          mul_nonneg (J.Pmin_nonneg T hT a b) (sq_nonneg (V b - V a))
    _ ≤ 2 * (V a) ^ 2 + (2 * M * K + M ^ 2 * Q) * T :=
        J.fluctuation_sq_le V hV hV' hK hM hK0 hQ hQ0 hT a F

end JumpSystem

/-! ## A concrete instance -/

namespace JumpSystem

/-- The two-state system `false → true` at rate `lam`, with `true` absorbing. -/
def twoState (lam : ℝ) (hlam : 0 ≤ lam) : JumpSystem Bool where
  ι := Unit
  rate _ b := if b then 0 else lam
  rate_nonneg _ b := by
    by_cases hb : b
    · simp [hb]
    · simp [hb, hlam]
  next _ b := !b

/-- The indicator of the state `true`. -/
def indTrue : Bool → ℝ := fun b => if b then 1 else 0

/-- **The drift of the indicator.** The drift of `1_{true}` is `lam` at `false` and `0` at `true`. -/
theorem drift_indTrue (lam : ℝ) (hlam : 0 ≤ lam) (b : Bool) :
    (twoState lam hlam).drift indTrue b = if b then 0 else lam := by
  show (∑ i : Unit, (twoState lam hlam).rate i b *
      (indTrue ((twoState lam hlam).next i b) - indTrue b)) = if b then 0 else lam
  simp [twoState, indTrue]
  by_cases hb : b = true
  · simp [hb]
  · have hbf : b = false := by
      cases b <;> simp_all
    simp [hbf]

/-- **The second moment of the indicator in the two-state system.** The mass that has reached
`true` by time `T` is at most `3 lam T`: the second-moment estimate of this module with `M = 1`,
`K = lam` (the drift bound of the indicator) and `Q = lam` (the exit rate bound). -/
theorem secondMoment_indTrue (lam : ℝ) (hlam : 0 ≤ lam) {T : ℝ} (hT : 0 ≤ T) :
    ∑ b ∈ ({false, true} : Finset Bool), (twoState lam hlam).Pmin T false b * (indTrue b) ^ 2
      ≤ (indTrue false) ^ 2 + (2 * 1 * lam + 1 ^ 2 * lam) * T := by
  have hq : ∀ b : Bool, (twoState lam hlam).q b ≤ lam := by
    intro b
    have hq' : (twoState lam hlam).q b = if b then 0 else lam := by
      show (∑ i : Unit, (twoState lam hlam).rate i b) = if b then 0 else lam
      simp [twoState]
    rw [hq']
    by_cases hb : b
    · simp [hb, hlam]
    · simp [hb]
  refine CRNT.JumpSystem.sum_Pmin_mul_sq_le_bounded (M := 1) (K := lam) (Q := lam)
    (twoState lam hlam) indTrue (fun b => ?_) (fun b => ?_) (fun b => ?_) (by norm_num) hlam hq
    hlam hT false ({false, true} : Finset Bool)
  · by_cases hb : b = true <;> simp [indTrue, hb]
  · by_cases hb : b = true <;> simp [indTrue, hb]
  · rw [drift_indTrue lam hlam b]
    by_cases hb : b = true
    · simp [hb, hlam]
    · have hbf : b = false := by cases b <;> simp_all
      simp [hbf]

end JumpSystem

/-! ## The bridge to the CRN chains -/

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **The jump system and the observable generator agree.** The drift of an observable under the
jump system of stochastic mass-action kinetics is the backward generator of the observable
(`CRNT.Network.observableGenerator`); the two differ only on disabled reactions, whose rate
vanishes. This identifies the drift of `CRNT/Stochastic/FosterLyapunov.lean` with the drift used
in this module, so that the second-moment estimates apply to the CRN chains. -/
theorem jumpSystem_drift_observableGenerator (N : Network S) (κ : RateConstants N)
    (f : (S → ℕ) → ℝ) (n : S → ℕ) :
    (N.jumpSystem κ).drift f n = N.observableGenerator κ f n := by
  unfold JumpSystem.drift observableGenerator
  simp only [jumpSystem]
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases hen : N.Enabled n r
  · have h1 : N.fireCount n r = N.jumpNextCount n r := by
      funext s
      simp [fireCount, jumpNextCount, hen]
    rw [h1]
  · rw [N.stochasticMassActionRate_eq_zero_of_not_enabled κ n r hen]
    simp only [zero_mul]

end Network

/-! ## Axioms -/

#print axioms CRNT.JumpSystem.drift_sq_le
#print axioms CRNT.JumpSystem.drift_sq_sub
#print axioms CRNT.JumpSystem.dynkin_sq_le_k
#print axioms CRNT.JumpSystem.dynkin_sq_le
#print axioms CRNT.JumpSystem.dynkin_sq_le_self
#print axioms CRNT.JumpSystem.sum_Pmin_mul_le_of_const_drift
#print axioms CRNT.JumpSystem.sum_Pmin_mul_sq_le
#print axioms CRNT.JumpSystem.sum_Pmin_mul_sq_le_bounded
#print axioms CRNT.JumpSystem.integral_sum_Pmin_mul_sq_le
#print axioms CRNT.JumpSystem.fluctuation_sq_le
#print axioms CRNT.JumpSystem.fluctuation_sq_le_lower
#print axioms CRNT.JumpSystem.fluctuation_chebyshev
#print axioms CRNT.Network.jumpSystem_drift_observableGenerator
#print axioms CRNT.JumpSystem.secondMoment_indTrue

end CRNT
