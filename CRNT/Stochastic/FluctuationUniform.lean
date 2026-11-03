import CRNT.Stochastic.CompensatedSecondMoment
import CRNT.Stochastic.CLTWeak

/-!
# The fluctuation-scale uniform-in-time estimate

## The mathematical background

Kurtz's law of large numbers for chemical reaction networks (Kurtz 1971, *On a class of finite
state Markov chains*, Ann. Probab. 1; Kurtz 1976, *Limit theorems for chemical reaction
networks*, Appl. Math. Optim. 16) says that the volume-scaled chain `X^V(t)/V` of a
stochastic mass-action network converges to the deterministic mass-action trajectory, and
that the **fluctuation** of the volume-scaled chain about that trajectory is of size
`O(V^{-1/2})`; the central limit theorem (Anderson and Kurtz 1979, *A rigorous local law of
large numbers for the multivariate chemical reaction network*, J. Theoret. Biol. 22) says
that the fluctuation, rescaled by `√V`, converges to a Gaussian law.  Both statements are
*fluctuation-scale* statements: the deviation of the chain from its deterministic
trajectory is measured at the scale of the central limit theorem, and the estimates
involving it have constants which do **not** grow with the volume `V`.

The uniform-in-time version of the fluctuation-scale estimate is the statement that, over a
fixed time window `[0, T]`, the fluctuation stays of size `O(1)` (after the central limit
rescaling) **uniformly in the initial state and uniformly in the time**, i.e. the
`sup_{t ≤ T}` of the relevant probability is bounded by a volume-independent constant.
This is the ingredient that leaf **P9** of `docs/field-map.md` (central limit theorem;
diffusion approximation) records as missing.

## What the repository already contains

* the **distributional** CLT for networks whose chains may explode
  (`CRNT.Network.multivariate_clt_open_weak`, `CRNT.Network.multivariate_clt_open_weak_integral`
  in `CRNT/Stochastic/CLTWeak.lean`): the fluctuation law of the volume-scaled chain is a
  sub-probability measure of mass `P(no explosion)`, completed to a probability measure and
  shown to converge weakly to the Gaussian `gaussLimit`;
* the **process-level statement in the path-free exit-mass form**
  (`CRNT.JumpSystem.mass_outside_le_exitMass`, `CRNT.JumpSystem.exitMass_mono`,
  `CRNT.Network.fluctuation_uniform_concentration`): the mass of the chain outside a set is
  bounded by the exit mass, the exit mass is non-decreasing in time, and the resulting
  uniform-in-time bound is proved.  This is the law-of-large-numbers scale: the exit mass is
  of size `O(1/V)` and hence bounds the mean square deviation by `O(1/V)`;
* the campaign's **second-moment modules**: `CRNT/Stochastic/FluctuationSecondMoment.lean`
  (the second moment of the Poisson fluctuation, `O(1/V)` at the fluctuation scale) and
  `CRNT/Stochastic/CompensatedSecondMoment.lean` (the compensated second-moment estimate for
  the jump system: `CRNT.JumpSystem.drift_sq_le`, `CRNT.JumpSystem.sum_Pmin_mul_sq_le`,
  `CRNT.JumpSystem.fluctuation_sq_le`, `CRNT.JumpSystem.fluctuation_chebyshev`).

## What this module adds

This module supplies the **fluctuation-scale (`O(1)`) uniform-in-time estimate** itself, in
the path-free (transition-function) form in which the library can state it.

The key new ingredient is the **increment-bounded second-moment drift**
(`CRNT.JumpSystem.drift_sq_le_inc`): if `0 ≤ V ≤ M`, the drift of `V` is bounded by `K`, and
the *increment* `|V(next i a) − V(a)|` of `V` along every active channel is bounded by `D`,
then

  `Q(V²)(a) ≤ 2 M K + D² q(a)`,

so the second moment of the *jumps* is controlled by the square of the bound of the
**increment** of the observable, and not by the square of the bound of the observable
itself.  This is what makes the estimate sharp at the fluctuation scale: for the
volume-scaled chain of a network the rate of a reaction is `O(V)` while the increment of a
count observable is `O(1)`, so `D² q(a) = O(1/V)` whereas `M² q(a) = O(V)`.

Combining this with the compensation identity `drift((V − c)²) = drift(V²) − 2 c QV`
(`CRNT.JumpSystem.drift_sq_sub`) gives the **centred second-moment drift**
(`CRNT.JumpSystem.drift_sq_sub_le`), and hence

* `CRNT.JumpSystem.fluctuation_sq_le_uniform`: the fluctuation-scale uniform-in-time
  estimate

  `∑_b Pmin(T)(a, b) (V b − V(a))² ≤ (2 M (K + L) + D² Q) T`,

  for `0 ≤ V ≤ M`, `−L ≤ QV ≤ K`, `|ΔV| ≤ D` on the active channels and `q ≤ Q`.  The
  constant does **not** depend on the starting state `a`, so the estimate is uniform in the
  initial state, and it holds for every `T`, so it is uniform in time;
* `CRNT.JumpSystem.fluctuation_sq_le_uniform_in_time`: the same estimate with the single
  constant valid for every time `t ∈ [0, T]`;
* `CRNT.JumpSystem.fluctuation_sq_le_uniform_scaled` and
  `CRNT.JumpSystem.fluctuation_chebyshev_uniform_scaled`: the estimate in the **scaled**
  (volume) convention, `∑_b Pmin(T)(a,b) ((V b − V a)/σ)² ≤ (2 (M/σ)((K+L)/σ) + (D/σ)² Q) T`.
  When `M`, `K + L` are `O(σ)`, `D = O(1)` and `Q = O(σ)` — the situation of a
  volume-scaled chemical reaction network with a count observable — the constant is `O(1)`,
  independently of the volume: **this is the `O(1)`-at-the-fluctuation-scale estimate**.
  The unscaled estimate has constant `O(σ)`, i.e. the unscaled fluctuation is `O(√σ)`;
* `CRNT.JumpSystem.fluctuation_chebyshev_uniform`: the Chebyshev (tail) form, uniform in the
  starting state and in the time;
* `CRNT.Network.fluctuation_uniform_concentration_of_second_moment` and
  `CRNT.Network.fluctuation_uniform_concentration_and_second_moment`: the bridge to the
  CRN chains — the fluctuation-scale uniform-in-time concentration of the volume-scaled
  chain, next to (and simultaneously with) the repository's exit-mass form
  `CRNT.Network.fluctuation_uniform_concentration`;
* `CRNT.JumpSystem.fluctuation_sq_le_uniform_unbounded`: the **exact degradation** when the
  Lyapunov function is unbounded: only the drift of the *square* can then be controlled
  (`drift(V²) ≤ C`), the estimate becomes `4 V(a)² + 2 C T`, it is no longer uniform in the
  starting state, and the constant `C` is not controlled by the drift of `V` at all
  (`CRNT.JumpSystem.drift_sq_twoState_scaled` exhibits this in the two-state system).

## What remains open

The **path-space** statement of leaf P9 is *not* proved here and cannot be: the library has
no i.i.d.-exponential measure, hence no exponential martingale, and no strong Markov
property, hence no optional stopping.  Two ingredients are missing in particular.

1. **The event identification.**  The path-free estimates bound the *mass* of the chain
   which is outside a set; to read them as the probability of the *event* "the chain leaves
   the set during the window" one has to identify the exit mass of the frozen chain with
   the probability of that event, which is what `CRNT/Stochastic/PathExitEvent.lean` and
   `CRNT/Stochastic/ExitMassIdentification.lean` set up but which needs an i.i.d.-exponential
   measure (the driving Poisson clock) to be carried out.
2. **The running supremum.**  The uniform-in-time statement
   `sup_{t ≤ T} P(|√V (X^V(t)/V − x(t))| > ε)` requires the *path* to be controlled over
   the whole window, which needs optional stopping of the compensated Poisson martingale
   along the random trajectory, and hence the strong Markov property.

Everything in this module is therefore a statement about the **path-free** quantities: the
minimal transition function `Pmin`, the exit mass (`CRNT.JumpSystem.exitMass`) and the
`f`-norm bounds built on them.  The estimates are fixed-time (and time-integrated) bounds
on the transition function, uniform in the initial state and in the time, and *not*
statements about sample paths.
-/

open MeasureTheory intervalIntegral Set Filter
open scoped BigOperators Topology

namespace CRNT
namespace JumpSystem

variable {α : Type*} [DecidableEq α] (J : JumpSystem α)

set_option maxHeartbeats 800000

/-! ## The increment-bounded second-moment drift -/

omit [DecidableEq α] in
/-- **The increment-bounded second-moment drift.**  If `0 ≤ V ≤ M`, the drift of `V` is
bounded by `K ≥ 0`, and the increment `|V(next i a) − V(a)|` of `V` along every *active*
channel (`rate i a ≠ 0`) is bounded by `D`, then

  `Q(V²)(a) = 2 V(a) QV(a) + ∑_i rate_i(a) (ΔV_i)² ≤ 2 M K + D² q(a)`.

The proof is the identity `(x² − y²) = 2 y (x − y) + (x − y)²` together with
`|ΔV_i| ≤ D`; the `D²` replaces the `M²` of `CRNT.JumpSystem.drift_sq_le`, and this is the
crucial gain at the fluctuation scale: for a volume-scaled chain the exit rate is `O(V)`
while the increment of a count observable is `O(1)`. -/
theorem drift_sq_le_inc (V : α → ℝ) {M K D : ℝ}
    (hV : ∀ a, 0 ≤ V a) (hV' : ∀ a, V a ≤ M) (hK : ∀ a, J.drift V a ≤ K) (hM : 0 ≤ M)
    (hK0 : 0 ≤ K) (hD : ∀ i a, J.rate i a ≠ 0 → |V (J.next i a) - V a| ≤ D) (hD0 : 0 ≤ D) :
    ∀ a, J.drift (fun b => V b ^ 2) a ≤ 2 * M * K + D ^ 2 * J.q a := by
  intro a
  have hsum : J.drift (fun b => V b ^ 2) a
      = 2 * V a * J.drift V a + ∑ i, J.rate i a * (V (J.next i a) - V a) ^ 2 := by
    simp only [drift]
    calc (∑ i, J.rate i a * ((V (J.next i a)) ^ 2 - (V a) ^ 2))
        = ∑ i, (J.rate i a * (2 * V a * (V (J.next i a) - V a))
            + J.rate i a * (V (J.next i a) - V a) ^ 2) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = (∑ i, J.rate i a * (2 * V a * (V (J.next i a) - V a)))
            + ∑ i, J.rate i a * (V (J.next i a) - V a) ^ 2 := Finset.sum_add_distrib
        _ = 2 * V a * (∑ i, J.rate i a * (V (J.next i a) - V a))
            + ∑ i, J.rate i a * (V (J.next i a) - V a) ^ 2 := by
          have h3 : (∑ i, J.rate i a * (2 * V a * (V (J.next i a) - V a)))
              = ∑ i, (2 * V a) * (J.rate i a * (V (J.next i a) - V a)) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
          rw [h3, ← Finset.mul_sum]
        _ = 2 * V a * J.drift V a + ∑ i, J.rate i a * (V (J.next i a) - V a) ^ 2 := by
          simp only [drift]
  rw [hsum]
  have hcore : V a * J.drift V a ≤ M * K := by
    rcases le_total (J.drift V a) 0 with hneg | hpos
    · have h2 : V a * J.drift V a ≤ 0 := by
        have := mul_nonpos_of_nonneg_of_nonpos (hV a) hneg
        linarith
      have h3 : 0 ≤ M * K := mul_nonneg hM hK0
      exact h2.trans h3
    · have h2 : V a * J.drift V a ≤ M * J.drift V a := by
        simpa [mul_comm] using mul_le_mul_of_nonneg_left (hV' a) hpos
      have h3 : M * J.drift V a ≤ M * K := mul_le_mul_of_nonneg_left (hK a) hM
      exact h2.trans h3
  calc (2 * V a * J.drift V a + ∑ i, J.rate i a * (V (J.next i a) - V a) ^ 2)
      ≤ 2 * M * K + ∑ i, J.rate i a * (V (J.next i a) - V a) ^ 2 := by
        refine add_le_add_left ?_ (∑ i, J.rate i a * (V (J.next i a) - V a) ^ 2)
        calc 2 * V a * J.drift V a = 2 * (V a * J.drift V a) := by ring
          _ ≤ 2 * (M * K) := mul_le_mul_of_nonneg_left hcore (by norm_num)
          _ = 2 * M * K := by ring
      _ ≤ 2 * M * K + ∑ i, J.rate i a * D ^ 2 := by
        refine add_le_add_right (Finset.sum_le_sum (s := Finset.univ) ?_) (2 * M * K)
        intro i _
        by_cases hr : J.rate i a = 0
        · simp [hr]
        · have hsq : (V (J.next i a) - V a) ^ 2 ≤ D ^ 2 :=
            sq_le_sq.mpr (by simpa [abs_of_nonneg hD0] using hD i a hr)
          exact mul_le_mul_of_nonneg_left hsq (J.rate_nonneg i a)
      _ = 2 * M * K + D ^ 2 * J.q a := by
        have h2 : (∑ i, J.rate i a * D ^ 2) = D ^ 2 * J.q a := by
          rw [← Finset.sum_mul]
          simp only [JumpSystem.q]
          ring
        rw [h2]

omit [DecidableEq α] in
/-- **The centred second-moment drift.**  Under the hypotheses of `drift_sq_le_inc`, and if
in addition the drift of `V` is bounded below by `−L`, then for every shift `c ∈ [0, M]`

  `Q((V − c)²)(a) ≤ 2 M (K + L) + D² q(a)`.

The bound is *uniform in the shift* `c`, which is what makes the fluctuation estimate of
`fluctuation_sq_le_uniform` uniform in the starting state. -/
theorem drift_sq_sub_le (V : α → ℝ) {M K L D : ℝ}
    (hV : ∀ a, 0 ≤ V a) (hV' : ∀ a, V a ≤ M) (hK : ∀ a, J.drift V a ≤ K) (hM : 0 ≤ M)
    (hK0 : 0 ≤ K) (hL : ∀ a, -L ≤ J.drift V a) (hL0 : 0 ≤ L)
    (hD : ∀ i a, J.rate i a ≠ 0 → |V (J.next i a) - V a| ≤ D) (hD0 : 0 ≤ D)
    (c : ℝ) (hc0 : 0 ≤ c) (hcM : c ≤ M) (a : α) :
    J.drift (fun b => (V b - c) ^ 2) a ≤ 2 * M * (K + L) + D ^ 2 * J.q a := by
  have h1 := J.drift_sq_le_inc V hV hV' hK hM hK0 hD hD0 a
  have h2 : -2 * c * J.drift V a ≤ 2 * c * L := by
    have h3 : 0 ≤ 2 * c := by linarith
    have h4 : -J.drift V a ≤ L := by linarith [hL a]
    have h5 : 2 * c * (-J.drift V a) ≤ 2 * c * L := mul_le_mul_of_nonneg_left h4 h3
    linarith
  have h6 : 2 * c * L ≤ 2 * M * L := by
    have h8 : c * L ≤ M * L := by
      simpa [mul_comm] using mul_le_mul_of_nonneg_left hcM hL0
    calc 2 * c * L = 2 * (c * L) := by ring
      _ ≤ 2 * (M * L) := mul_le_mul_of_nonneg_left h8 (by norm_num)
      _ = 2 * M * L := by ring
  calc J.drift (fun b => (V b - c) ^ 2) a
      = J.drift (fun b => V b ^ 2) a - 2 * c * J.drift V a := J.drift_sq_sub V c a
    _ ≤ (2 * M * K + D ^ 2 * J.q a) - 2 * c * J.drift V a := by linarith [h1]
    _ ≤ (2 * M * K + 2 * M * L) + D ^ 2 * J.q a := by linarith [h2, h6]
    _ = 2 * M * (K + L) + D ^ 2 * J.q a := by ring

omit [DecidableEq α] in
/-- The drift of a scaled observable is the drift of the observable, divided by the scale. -/
theorem drift_div (V : α → ℝ) (σ : ℝ) (a : α) :
    J.drift (fun b => V b / σ) a = J.drift V a / σ := by
  simp only [drift]
  calc (∑ i, J.rate i a * (V (J.next i a) / σ - V a / σ))
      = ∑ i, J.rate i a * ((V (J.next i a) - V a) / σ) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
    _ = ∑ i, (J.rate i a * (V (J.next i a) - V a)) / σ := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (∑ i, J.rate i a * (V (J.next i a) - V a)) / σ := by
      rw [Finset.sum_div]
    _ = J.drift V a / σ := rfl

/-! ## The fluctuation-scale uniform-in-time estimate -/

/-- **The fluctuation-scale (`O(1)`) uniform-in-time estimate.**  Let `J` be a jump system,
`V` a Lyapunov function with `0 ≤ V ≤ M`, with drift bounded by `K ≥ 0` and bounded below by
`−L`, with increments `|V(next i a) − V(a)|` bounded by `D` on the active channels, and let
the exit rate be bounded by `Q`.  Then for every `T ≥ 0` and every starting state `a`,

  `∑_b Pmin(T)(a, b) (V b − V(a))² ≤ (2 M (K + L) + D² Q) T`.

The estimate is **uniform in the starting state** (the constant does not involve `a`) and
**uniform in time** (it holds for every `T`, with the same constant).  In the scaled
(volume) convention — the observable divided by the volume `σ` — the constant becomes
`2 (M/σ)((K+L)/σ) + (D/σ)² Q`, which is `O(1)` and *independent of the volume* when
`M, K + L = O(σ)`, `D = O(1)` and `Q = O(σ)`: the situation of a volume-scaled chemical
reaction network with a count observable.  This is the `O(1)`-at-the-fluctuation-scale
estimate of leaf P9.

The proof is the Dynkin inequality for the square of the *deviation* `V − V(a)` — whose
drift is bounded by `2 M (K + L) + D² Q` uniformly in the shift, see
`CRNT.JumpSystem.drift_sq_sub_le` — applied to
`CRNT.JumpSystem.sum_Pmin_mul_le_of_const_drift`. -/
theorem fluctuation_sq_le_uniform (V : α → ℝ) {M K L D Q : ℝ}
    (hV : ∀ a, 0 ≤ V a) (hV' : ∀ a, V a ≤ M) (hM : 0 ≤ M)
    (hK : ∀ a, J.drift V a ≤ K) (hK0 : 0 ≤ K)
    (hL : ∀ a, -L ≤ J.drift V a) (hL0 : 0 ≤ L)
    (hD : ∀ i a, J.rate i a ≠ 0 → |V (J.next i a) - V a| ≤ D) (hD0 : 0 ≤ D)
    (hQ : ∀ a, J.q a ≤ Q) (hQ0 : 0 ≤ Q)
    {T : ℝ} (hT : 0 ≤ T) (a : α) (F : Finset α) :
    ∑ b ∈ F, J.Pmin T a b * (V b - V a) ^ 2 ≤ (2 * M * (K + L) + D ^ 2 * Q) * T := by
  have hC : 0 ≤ 2 * M * (K + L) + D ^ 2 * Q := by positivity
  have hdrift : ∀ c, J.drift (fun b => (V b - V a) ^ 2) c
      ≤ 2 * M * (K + L) + D ^ 2 * Q := by
    intro c
    have h1 := J.drift_sq_sub_le V hV hV' hK hM hK0 hL hL0 hD hD0 (V a) (hV a) (hV' a) c
    have h2 : D ^ 2 * J.q c ≤ D ^ 2 * Q := mul_le_mul_of_nonneg_left (hQ c) (sq_nonneg D)
    linarith
  have h := J.sum_Pmin_mul_le_of_const_drift (fun b => (V b - V a) ^ 2)
    (fun b => sq_nonneg _) hC hdrift hT a F
  rw [show (V a - V a) ^ 2 = 0 by ring] at h
  linarith


/-- **The fluctuation-scale estimate without an increment hypothesis.**  If `0 ≤ V ≤ M`, then
the increment of `V` along any channel is at most `M`, and the estimate of this module
specialises to

  `∑_b Pmin(T)(a, b) (V b − V a)² ≤ (2 M (K + L) + M² Q) T`.

This is the form in which the estimate is *uniform in the starting state*: the constant does
not depend on `a` at all. -/
theorem fluctuation_sq_le_uniform_of_bounded (V : α → ℝ) {M K L Q : ℝ}
    (hV : ∀ a, 0 ≤ V a) (hV' : ∀ a, V a ≤ M) (hM : 0 ≤ M)
    (hK : ∀ a, J.drift V a ≤ K) (hK0 : 0 ≤ K)
    (hL : ∀ a, -L ≤ J.drift V a) (hL0 : 0 ≤ L)
    (hQ : ∀ a, J.q a ≤ Q) (hQ0 : 0 ≤ Q)
    {T : ℝ} (hT : 0 ≤ T) (a : α) (F : Finset α) :
    ∑ b ∈ F, J.Pmin T a b * (V b - V a) ^ 2 ≤ (2 * M * (K + L) + M ^ 2 * Q) * T := by
  have hD : ∀ i a, J.rate i a ≠ 0 → |V (J.next i a) - V a| ≤ M := by
    intro i a _
    have h1 : -M ≤ V (J.next i a) - V a := by
      linarith [hV (J.next i a), hV' a]
    have h2 : V (J.next i a) - V a ≤ M := by
      linarith [hV' (J.next i a), hV a]
    exact abs_le.mpr ⟨h1, h2⟩
  exact J.fluctuation_sq_le_uniform V hV hV' hM hK hK0 hL hL0 hD hM hQ hQ0 hT a F

/-- **The uniform-in-time form of the fluctuation-scale estimate.**  For every time
`t ∈ [0, T]`, the second moment of the fluctuation of `V` about its initial value is bounded
by the *same* constant `(2 M (K + L) + D² Q) T`.  This is the form in which the estimate
controls a whole time window at once. -/
theorem fluctuation_sq_le_uniform_in_time (V : α → ℝ) {M K L D Q : ℝ}
    (hV : ∀ a, 0 ≤ V a) (hV' : ∀ a, V a ≤ M) (hM : 0 ≤ M)
    (hK : ∀ a, J.drift V a ≤ K) (hK0 : 0 ≤ K)
    (hL : ∀ a, -L ≤ J.drift V a) (hL0 : 0 ≤ L)
    (hD : ∀ i a, J.rate i a ≠ 0 → |V (J.next i a) - V a| ≤ D) (hD0 : 0 ≤ D)
    (hQ : ∀ a, J.q a ≤ Q) (hQ0 : 0 ≤ Q)
    {T : ℝ} (hT : 0 ≤ T) (a : α) (F : Finset α) :
    ∀ t ∈ Icc 0 T,
      ∑ b ∈ F, J.Pmin t a b * (V b - V a) ^ 2 ≤ (2 * M * (K + L) + D ^ 2 * Q) * T := by
  intro t ht
  have h1 := J.fluctuation_sq_le_uniform V hV hV' hM hK hK0 hL hL0 hD hD0 hQ hQ0 ht.1 a F
  have h3 : 0 ≤ 2 * M * (K + L) + D ^ 2 * Q := by positivity
  have h2 : (2 * M * (K + L) + D ^ 2 * Q) * t ≤ (2 * M * (K + L) + D ^ 2 * Q) * T :=
    mul_le_mul_of_nonneg_left (by linarith [ht.2]) h3
  have h4 : 0 ≤ (2 * M * (K + L) + D ^ 2 * Q) * T := mul_nonneg h3 hT
  linarith

/-- **The fluctuation-scale estimate in the scaled (volume) convention.**  For a scale
`σ > 0`,

  `∑_b Pmin(T)(a, b) ((V b − V(a)) / σ)² ≤ (2 (M/σ) ((K+L)/σ) + (D/σ)² Q) T`.

For a volume-scaled chemical reaction network with a count observable, `M = O(σ)`,
`K + L = O(σ)`, `D = O(1)` and `Q = O(σ)`, so the constant is `O(1)`, independently of the
volume: the fluctuation of the *scaled* observable stays at the fluctuation scale over a
fixed time window, uniformly in the initial state.  The unscaled estimate has constant
`O(σ)`, i.e. it grows with the volume: this is the scaling caveat that the `O(1)` statement
must be read with. -/
theorem fluctuation_sq_le_uniform_scaled (V : α → ℝ) (σ : ℝ) (hσ : 0 < σ) {M K L D Q : ℝ}
    (hV : ∀ a, 0 ≤ V a) (hV' : ∀ a, V a ≤ M) (hM : 0 ≤ M)
    (hK : ∀ a, J.drift V a ≤ K) (hK0 : 0 ≤ K)
    (hL : ∀ a, -L ≤ J.drift V a) (hL0 : 0 ≤ L)
    (hD : ∀ i a, J.rate i a ≠ 0 → |V (J.next i a) - V a| ≤ D) (hD0 : 0 ≤ D)
    (hQ : ∀ a, J.q a ≤ Q) (hQ0 : 0 ≤ Q)
    {T : ℝ} (hT : 0 ≤ T) (a : α) (F : Finset α) :
    ∑ b ∈ F, J.Pmin T a b * ((V b - V a) / σ) ^ 2
      ≤ (2 * (M / σ) * ((K + L) / σ) + (D / σ) ^ 2 * Q) * T := by
  have hV0 : ∀ a, 0 ≤ V a / σ := fun a => div_nonneg (hV a) hσ.le
  have hV1 : ∀ a, V a / σ ≤ M / σ := fun a => (div_le_div_iff_of_pos_right hσ).2 (hV' a)
  have hM0 : 0 ≤ M / σ := div_nonneg hM hσ.le
  have hK0' : ∀ a, J.drift (fun b => V b / σ) a ≤ K / σ := by
    intro a
    rw [J.drift_div V σ a]
    exact (div_le_div_iff_of_pos_right hσ).2 (hK a)
  have hK1 : 0 ≤ K / σ := div_nonneg hK0 hσ.le
  have hL0' : ∀ a, -(L / σ) ≤ J.drift (fun b => V b / σ) a := by
    intro a
    rw [J.drift_div V σ a]
    refine (le_div_iff₀ hσ).2 ?_
    have h2 : -(L / σ) * σ = -L := by rw [neg_mul, div_mul_cancel₀ L hσ.ne']
    rw [h2]
    exact hL a
  have hL1 : 0 ≤ L / σ := div_nonneg hL0 hσ.le
  have hD0' : ∀ i a, J.rate i a ≠ 0 → |V (J.next i a) / σ - V a / σ| ≤ D / σ := by
    intro i a hr
    have h1 : V (J.next i a) / σ - V a / σ = (V (J.next i a) - V a) / σ := by ring
    rw [h1, abs_div, abs_of_nonneg hσ.le]
    refine (div_le_div_iff_of_pos_right hσ).2 ?_
    simpa [abs_of_nonneg hD0] using hD i a hr
  have hD1 : 0 ≤ D / σ := div_nonneg hD0 hσ.le
  have hmain := J.fluctuation_sq_le_uniform (fun b => V b / σ) hV0 hV1 hM0 hK0' hK1 hL0' hL1
    hD0' hD1 hQ hQ0 hT a F
  have heq : (∑ b ∈ F, J.Pmin T a b * ((V b - V a) / σ) ^ 2)
      = ∑ b ∈ F, J.Pmin T a b * ((V b / σ) - (V a / σ)) ^ 2 := by
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [← heq] at hmain
  simpa [add_div] using hmain

/-! ## The Chebyshev form -/

/-- **The fluctuation-scale Chebyshev bound, uniform in the starting state and in the
time.**  If the observable `V` deviates from its initial value by at least `δ > 0` at the
state `b`, then the mass of such states is at most

  `∑_{b ∈ G} Pmin(T)(a, b) ≤ (2 M (K + L) + D² Q) T / δ²`.

This is the tail form of `fluctuation_sq_le_uniform`; it is the path-free analogue of
`CRNT.Stochastic.fluctScale_meas_aggregate_scaledClock_ge_le`, the fluctuation-scale
Chebyshev bound of the Poisson fluctuation. -/
theorem fluctuation_chebyshev_uniform (V : α → ℝ) {M K L D Q : ℝ}
    (hV : ∀ a, 0 ≤ V a) (hV' : ∀ a, V a ≤ M) (hM : 0 ≤ M)
    (hK : ∀ a, J.drift V a ≤ K) (hK0 : 0 ≤ K)
    (hL : ∀ a, -L ≤ J.drift V a) (hL0 : 0 ≤ L)
    (hD : ∀ i a, J.rate i a ≠ 0 → |V (J.next i a) - V a| ≤ D) (hD0 : 0 ≤ D)
    (hQ : ∀ a, J.q a ≤ Q) (hQ0 : 0 ≤ Q)
    {T : ℝ} (hT : 0 ≤ T) (a : α) (F : Finset α) {δ : ℝ} (hδ : 0 < δ)
    (G : Finset α) (hGF : G ⊆ F) (hG : ∀ b ∈ G, δ ≤ |V b - V a|) :
    ∑ b ∈ G, J.Pmin T a b ≤ (2 * M * (K + L) + D ^ 2 * Q) * T / δ ^ 2 := by
  have hsq : ∀ b ∈ G, δ ^ 2 ≤ (V b - V a) ^ 2 := by
    intro b hb
    have h1 : δ ^ 2 ≤ |V b - V a| ^ 2 :=
      (sq_le_sq).2 (by simpa [abs_of_pos hδ] using hG b hb)
    have h2 : |V b - V a| ^ 2 = (V b - V a) ^ 2 := sq_abs _
    linarith
  rw [le_div_iff₀ (sq_pos_of_pos hδ)]
  calc (∑ b ∈ G, J.Pmin T a b) * δ ^ 2
      = ∑ b ∈ G, J.Pmin T a b * δ ^ 2 := by rw [Finset.sum_mul]
    _ ≤ ∑ b ∈ G, J.Pmin T a b * (V b - V a) ^ 2 := by
      refine Finset.sum_le_sum fun b hb => ?_
      exact mul_le_mul_of_nonneg_left (hsq b hb) (J.Pmin_nonneg T hT a b)
    _ ≤ ∑ b ∈ F, J.Pmin T a b * (V b - V a) ^ 2 := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hGF fun b _ _ =>
        mul_nonneg (J.Pmin_nonneg T hT a b) (sq_nonneg (V b - V a))
    _ ≤ (2 * M * (K + L) + D ^ 2 * Q) * T :=
      J.fluctuation_sq_le_uniform V hV hV' hM hK hK0 hL hL0 hD hD0 hQ hQ0 hT a F

/-- **The Chebyshev bound in the scaled (volume) convention.**  The tail form of
`fluctuation_sq_le_uniform_scaled`: the mass of the states at which the *scaled* observable
deviates from its initial value by at least `δ` is at most

  `(2 (M/σ) ((K+L)/σ) + (D/σ)² Q) T / δ²`. -/
theorem fluctuation_chebyshev_uniform_scaled (V : α → ℝ) (σ : ℝ) (hσ : 0 < σ) {M K L D Q : ℝ}
    (hV : ∀ a, 0 ≤ V a) (hV' : ∀ a, V a ≤ M) (hM : 0 ≤ M)
    (hK : ∀ a, J.drift V a ≤ K) (hK0 : 0 ≤ K)
    (hL : ∀ a, -L ≤ J.drift V a) (hL0 : 0 ≤ L)
    (hD : ∀ i a, J.rate i a ≠ 0 → |V (J.next i a) - V a| ≤ D) (hD0 : 0 ≤ D)
    (hQ : ∀ a, J.q a ≤ Q) (hQ0 : 0 ≤ Q)
    {T : ℝ} (hT : 0 ≤ T) (a : α) (F : Finset α) {δ : ℝ} (hδ : 0 < δ)
    (G : Finset α) (hGF : G ⊆ F) (hG : ∀ b ∈ G, δ ≤ |V b - V a| / σ) :
    ∑ b ∈ G, J.Pmin T a b ≤ (2 * (M / σ) * ((K + L) / σ) + (D / σ) ^ 2 * Q) * T / δ ^ 2 := by
  have hV0 : ∀ a, 0 ≤ V a / σ := fun a => div_nonneg (hV a) hσ.le
  have hV1 : ∀ a, V a / σ ≤ M / σ := fun a => (div_le_div_iff_of_pos_right hσ).2 (hV' a)
  have hM0 : 0 ≤ M / σ := div_nonneg hM hσ.le
  have hK0' : ∀ a, J.drift (fun b => V b / σ) a ≤ K / σ := by
    intro a
    rw [J.drift_div V σ a]
    exact (div_le_div_iff_of_pos_right hσ).2 (hK a)
  have hK1 : 0 ≤ K / σ := div_nonneg hK0 hσ.le
  have hL0' : ∀ a, -(L / σ) ≤ J.drift (fun b => V b / σ) a := by
    intro a
    rw [J.drift_div V σ a]
    refine (le_div_iff₀ hσ).2 ?_
    have h2 : -(L / σ) * σ = -L := by rw [neg_mul, div_mul_cancel₀ L hσ.ne']
    rw [h2]
    exact hL a
  have hL1 : 0 ≤ L / σ := div_nonneg hL0 hσ.le
  have hD0' : ∀ i a, J.rate i a ≠ 0 → |V (J.next i a) / σ - V a / σ| ≤ D / σ := by
    intro i a hr
    have h1 : V (J.next i a) / σ - V a / σ = (V (J.next i a) - V a) / σ := by ring
    rw [h1, abs_div, abs_of_nonneg hσ.le]
    refine (div_le_div_iff_of_pos_right hσ).2 ?_
    simpa [abs_of_nonneg hD0] using hD i a hr
  have hD1 : 0 ≤ D / σ := div_nonneg hD0 hσ.le
  have hmain := J.fluctuation_chebyshev_uniform (fun b => V b / σ) hV0 hV1 hM0 hK0' hK1 hL0' hL1
    hD0' hD1 hQ hQ0 hT a F hδ G hGF (by
      intro b hb
      have h1 := hG b hb
      have h2 : |V b - V a| / σ = |(V b - V a) / σ| := by
        rw [abs_div]
        simp [abs_of_nonneg hσ.le]
      have h3 : |V b / σ - V a / σ| = |(V b - V a) / σ| := by
        congr 1
        ring
      rw [h2, ← h3] at h1
      exact h1)
  simpa [add_div] using hmain

/-! ## The unbounded case: the exact degradation -/

/-- **The unbounded case: the exact degradation.**  If the Lyapunov function is unbounded,
the only hypothesis available is a bound `C` on the drift of its *square*; then

  `∑_b Pmin(T)(a, b) (V b − V(a))² ≤ 4 V(a)² + 2 C T`.

Two things are lost with respect to the bounded case: the estimate is no longer uniform in
the starting state (the term `4 V(a)²`), and the constant `2 C` is *not* controlled by the
drift of `V` — it is the drift of `V²` which is controlled, and for an unbounded observable
the latter is itself unbounded (`CRNT.JumpSystem.drift_sq_twoState_scaled`).  In the scaled
convention the constant of the bounded case is `O(1)` (the fluctuation scale), while here
the coefficient of `T` is not bounded in terms of the volume: the bound degrades to the
`O(T)` statement. -/
theorem fluctuation_sq_le_uniform_unbounded (V : α → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hdrift : ∀ a, J.drift (fun b => V b ^ 2) a ≤ C)
    {T : ℝ} (hT : 0 ≤ T) (a : α) (F : Finset α) :
    ∑ b ∈ F, J.Pmin T a b * (V b - V a) ^ 2 ≤ 4 * (V a) ^ 2 + 2 * C * T := by
  have hsq : ∀ b : α, (V b - V a) ^ 2 ≤ 2 * (V b) ^ 2 + 2 * (V a) ^ 2 := by
    intro b
    have h2 : 0 ≤ (V b + V a) ^ 2 := sq_nonneg _
    have h3 : 2 * (V b) ^ 2 + 2 * (V a) ^ 2 - (V b - V a) ^ 2 = (V b + V a) ^ 2 := by ring
    linarith
  have h1 := J.sum_Pmin_mul_sq_le V hC hdrift hT a F
  have h2 : ∑ b ∈ F, J.Pmin T a b ≤ 1 := J.sum_Pmin_le_one T hT a F
  calc (∑ b ∈ F, J.Pmin T a b * (V b - V a) ^ 2)
      ≤ ∑ b ∈ F, J.Pmin T a b * (2 * (V b) ^ 2 + 2 * (V a) ^ 2) := by
        refine Finset.sum_le_sum fun b _ => ?_
        exact mul_le_mul_of_nonneg_left (hsq b) (J.Pmin_nonneg T hT a b)
    _ = 2 * (∑ b ∈ F, J.Pmin T a b * (V b) ^ 2)
        + 2 * (V a) ^ 2 * (∑ b ∈ F, J.Pmin T a b) := by
        calc (∑ b ∈ F, J.Pmin T a b * (2 * (V b) ^ 2 + 2 * (V a) ^ 2))
            = (∑ b ∈ F, J.Pmin T a b * (2 * (V b) ^ 2))
              + (∑ b ∈ F, J.Pmin T a b * (2 * (V a) ^ 2)) := by
                have h5 : (∑ b ∈ F, J.Pmin T a b * (2 * (V b) ^ 2 + 2 * (V a) ^ 2))
                    = ∑ b ∈ F, (J.Pmin T a b * (2 * (V b) ^ 2)
                        + J.Pmin T a b * (2 * (V a) ^ 2)) := by
                  apply Finset.sum_congr rfl
                  intro b _
                  ring
                rw [h5, Finset.sum_add_distrib]
            _ = 2 * (∑ b ∈ F, J.Pmin T a b * (V b) ^ 2)
              + 2 * (V a) ^ 2 * (∑ b ∈ F, J.Pmin T a b) := by
              have h3 : (∑ b ∈ F, J.Pmin T a b * (2 * (V b) ^ 2))
                  = 2 * (∑ b ∈ F, J.Pmin T a b * (V b) ^ 2) := by
                calc (∑ b ∈ F, J.Pmin T a b * (2 * (V b) ^ 2))
                    = ∑ b ∈ F, 2 * (J.Pmin T a b * (V b) ^ 2) := by
                        apply Finset.sum_congr rfl
                        intro b _
                        ring
                    _ = 2 * (∑ b ∈ F, J.Pmin T a b * (V b) ^ 2) := by
                        rw [Finset.mul_sum]
              have h4 : (∑ b ∈ F, J.Pmin T a b * (2 * (V a) ^ 2))
                  = 2 * (V a) ^ 2 * (∑ b ∈ F, J.Pmin T a b) := by
                calc (∑ b ∈ F, J.Pmin T a b * (2 * (V a) ^ 2))
                    = ∑ b ∈ F, 2 * (J.Pmin T a b * (V a) ^ 2) := by
                        apply Finset.sum_congr rfl
                        intro b _
                        ring
                    _ = 2 * (∑ b ∈ F, J.Pmin T a b * (V a) ^ 2) := by
                        rw [Finset.mul_sum]
                    _ = 2 * (V a) ^ 2 * (∑ b ∈ F, J.Pmin T a b) := by
                        rw [← Finset.sum_mul]
                        ring
              rw [h3, h4]
    _ ≤ 2 * ((V a) ^ 2 + C * T) + 2 * (V a) ^ 2 := by
        have h5 : (V a) ^ 2 * (∑ b ∈ F, J.Pmin T a b) ≤ (V a) ^ 2 := by
          have := mul_le_mul_of_nonneg_left h2 (sq_nonneg (V a))
          simpa using this
        have h7 : 2 * (∑ b ∈ F, J.Pmin T a b * (V b) ^ 2) ≤ 2 * ((V a) ^ 2 + C * T) :=
          mul_le_mul_of_nonneg_left h1 (by norm_num)
        have h8 : 2 * (V a) ^ 2 * (∑ b ∈ F, J.Pmin T a b) ≤ 2 * (V a) ^ 2 := by
          have hx := mul_le_mul_of_nonneg_left h5 (by norm_num : (0 : ℝ) ≤ 2)
          simpa [mul_assoc] using hx
        linarith
    _ = 4 * (V a) ^ 2 + 2 * C * T := by ring

end JumpSystem
end CRNT

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

set_option maxHeartbeats 800000

/-! ## The bridge to the CRN chains -/

/-- **The exit rate of the volume-scaled chain is the volume times the per-volume exit
rate.**  For the chain of the volume-scaled network (`CRNT.Network.volumeScale`) the exit
rate is `V · ∑_r densRate κ V r c`: the propensity of a reaction is `V` times its
density-dependent rate.  This is the reason why the *increment* bound `D` (rather than the
bound `M` of the observable) is the relevant one at the fluctuation scale. -/
theorem jumpSystem_q_volumeScale (N : Network S) (κ : RateConstants N) {V : ℝ} (hV : 0 < V)
    (c : S → ℕ) :
    (N.jumpSystem (N.volumeScale κ V hV)).q c = V * ∑ r, N.densRate κ V r c := by
  calc (N.jumpSystem (N.volumeScale κ V hV)).q c = N.exitRate (N.volumeScale κ V hV) c :=
      N.jumpSystem_q _ _
    _ = ∑ r, N.stochasticMassActionRate (N.volumeScale κ V hV) c r := rfl
    _ = ∑ r, (V * N.densRate κ V r c) := by
      refine Finset.sum_congr rfl fun r _ => ?_
      exact N.stochasticRate_volumeScale κ hV c r
    _ = V * ∑ r, N.densRate κ V r c := by rw [Finset.mul_sum]

/-- **A bound on the stoichiometric increment of a species**: the sum of the absolute
values of the stoichiometric increments of the species over all reactions. -/
def stoichBound (N : Network S) (s : S) : ℝ := ∑ r, |N.reactionVector r s|

/-- The stoichiometric bound is nonnegative. -/
theorem stoichBound_nonneg (N : Network S) (s : S) : 0 ≤ N.stoichBound s := by
  unfold stoichBound
  exact Finset.sum_nonneg fun r _ => abs_nonneg _

/-- Each stoichiometric increment of a species is bounded by `stoichBound`. -/
theorem stoichBound_le (N : Network S) (s : S) (r : N.R) :
    |N.reactionVector r s| ≤ N.stoichBound s := by
  unfold stoichBound
  exact Finset.single_le_sum (f := fun r => |N.reactionVector r s|)
    (fun r _ => abs_nonneg _) (Finset.mem_univ r)

/-- **The density of a species**: the count divided by the volume.  This is the observable
at the fluctuation scale: its bound `M` is `O(1)` (the density bound), its drift is `O(1)`
(the per-volume drift) and its increment is `O(1/V)` (one molecule). -/
noncomputable def densityObservable (V : ℝ) (s : S) : (S → ℕ) → ℝ := fun c => (c s : ℝ) / V

/-- **A positive propensity forces the reaction to be enabled.** -/
theorem stochasticMassActionRate_ne_zero_imp_Enabled (N : Network S) (κ : RateConstants N)
    {n : S → ℕ} {r : N.R} (hr : N.stochasticMassActionRate κ n r ≠ 0) : N.Enabled n r := by
  by_contra hn
  have hz := N.stochasticMassActionRate_eq_zero_of_not_enabled κ n r hn
  rw [hz] at hr
  exact hr rfl

/-- **The increment of the density along a reaction.**  If the reaction `r` is enabled at
`c`, the density of the species `s` changes by the stoichiometric increment divided by the
volume: `densityObservable V s (jumpNextCount c r) − densityObservable V s c =
reactionVector r s / V`. -/
theorem densityObservable_jumpNextCount_sub (N : Network S) (V : ℝ) (s : S)
    (c : S → ℕ) (r : N.R) (hen : N.Enabled c r) :
    densityObservable V s (N.jumpNextCount c r) - densityObservable V s c
      = N.reactionVector r s / V := by
  have h1 : N.jumpNextCount c r s = c s - (N.reaction r).source s + (N.reaction r).target s := rfl
  have h2 : ((N.jumpNextCount c r) s : ℝ)
      = (c s : ℝ) - ((N.reaction r).source s : ℝ) + ((N.reaction r).target s : ℝ) := by
    rw [h1, Nat.cast_add, Nat.cast_sub (hen s)]
  unfold densityObservable
  rw [h2, Network.reactionVector_apply]
  ring

/-- **The increment of the density is bounded by the stoichiometric bound.**  The increment
of the density of a species along an enabled reaction is at most `stoichBound s / V`: this
is the `D = O(1/V)` of the fluctuation-scale estimate, in contrast with the `M = O(1)` of
the density itself. -/
theorem densityObservable_increment_bound (N : Network S) {V : ℝ} (hV : 0 < V) (s : S)
    (c : S → ℕ) (r : N.R) (hen : N.Enabled c r) :
    |densityObservable V s (N.jumpNextCount c r) - densityObservable V s c|
      ≤ N.stoichBound s / V := by
  have h1 := N.densityObservable_jumpNextCount_sub V s c r hen
  rw [h1, abs_div, abs_of_nonneg hV.le]
  have h2 : |N.reactionVector r s| ≤ N.stoichBound s := N.stoichBound_le s r
  exact div_le_div_of_nonneg_right h2 hV.le


/-- **The new second-moment estimate implies a uniform-in-time fluctuation concentration
bound for the volume-scaled chain.**  Let `f` be an observable of the volume-scaled chain
of volume `V` which is bounded by `M`, whose drift is bounded by `K` above and by `−L`
below, whose increment along an enabled reaction is bounded by `D`, and whose exit rate is
bounded by `V · Q₀` (the per-volume exit rate is bounded by `Q₀`).  Then for every
`T ≥ 0`, every starting state `a` and every set `G` of states at which `f` deviates from
its initial value by at least `ε > 0`,

  `∑_{b ∈ G} Pmin^V(T)(a, b) ≤ (2 M (K + L) + D² V Q₀) T / ε²`.

The bound is uniform in the starting state and in the time, and its constant is
independent of the volume whenever `M, K + L = O(1)` and `D = O(1/V)` — the situation of a
species density.  This is the fluctuation-scale counterpart of the repository's
`CRNT.Network.fluctuation_uniform_concentration`, whose exit-mass bound is at the
law-of-large-numbers scale. -/
theorem fluctuation_uniform_concentration_of_second_moment
    (N : Network S) (κ : RateConstants N) {V : ℝ} (hV : 0 < V) (f : (S → ℕ) → ℝ)
    {M K L D Q₀ : ℝ}
    (hf0 : ∀ c, 0 ≤ f c) (hfM : ∀ c, f c ≤ M) (hM : 0 ≤ M)
    (hK : ∀ c, (N.jumpSystem (N.volumeScale κ V hV)).drift f c ≤ K) (hK0 : 0 ≤ K)
    (hL : ∀ c, -L ≤ (N.jumpSystem (N.volumeScale κ V hV)).drift f c) (hL0 : 0 ≤ L)
    (hD : ∀ r c, N.Enabled c r → |f (N.jumpNextCount c r) - f c| ≤ D) (hD0 : 0 ≤ D)
    (hQ : ∀ c, (N.jumpSystem (N.volumeScale κ V hV)).q c ≤ V * Q₀) (hQ0 : 0 ≤ Q₀)
    {T : ℝ} (hT : 0 ≤ T) (a : S → ℕ) (F : Finset (S → ℕ)) {ε : ℝ} (hε : 0 < ε)
    (G : Finset (S → ℕ)) (hGF : G ⊆ F) (hG : ∀ b ∈ G, ε ≤ |f b - f a|) :
    ∑ b ∈ G, (N.jumpSystem (N.volumeScale κ V hV)).Pmin T a b
      ≤ (2 * M * (K + L) + D ^ 2 * V * Q₀) * T / ε ^ 2 := by
  have hD' : ∀ i a, (N.jumpSystem (N.volumeScale κ V hV)).rate i a ≠ 0 →
      |f ((N.jumpSystem (N.volumeScale κ V hV)).next i a) - f a| ≤ D := by
    intro i a hr
    have hen : N.Enabled a i := by
      refine N.stochasticMassActionRate_ne_zero_imp_Enabled (κ := N.volumeScale κ V hV)
        (n := a) (r := i) ?_
      exact hr
    show |f (N.jumpNextCount a i) - f a| ≤ D
    exact hD i a hen
  have hQ0' : 0 ≤ V * Q₀ := mul_nonneg hV.le hQ0
  have hmain := JumpSystem.fluctuation_chebyshev_uniform (N.jumpSystem (N.volumeScale κ V hV))
    f hf0 hfM hM hK hK0 hL hL0 hD' hD0 hQ hQ0' hT a F hε G hGF hG
  simpa [mul_assoc] using hmain

/-- **The uniform-in-time form of the fluctuation-scale concentration.**  For every time
`τ ∈ [0, T]` the mass of the chain whose observable deviates from its initial value by at
least `ε` is bounded by the *same* constant `(2 M (K + L) + D² V Q₀) T / ε²`: the estimate
controls a whole time window at once. -/
theorem fluctuation_uniform_concentration_of_second_moment_uniform_in_time
    (N : Network S) (κ : RateConstants N) {V : ℝ} (hV : 0 < V) (f : (S → ℕ) → ℝ)
    {M K L D Q₀ : ℝ}
    (hf0 : ∀ c, 0 ≤ f c) (hfM : ∀ c, f c ≤ M) (hM : 0 ≤ M)
    (hK : ∀ c, (N.jumpSystem (N.volumeScale κ V hV)).drift f c ≤ K) (hK0 : 0 ≤ K)
    (hL : ∀ c, -L ≤ (N.jumpSystem (N.volumeScale κ V hV)).drift f c) (hL0 : 0 ≤ L)
    (hD : ∀ r c, N.Enabled c r → |f (N.jumpNextCount c r) - f c| ≤ D) (hD0 : 0 ≤ D)
    (hQ : ∀ c, (N.jumpSystem (N.volumeScale κ V hV)).q c ≤ V * Q₀) (hQ0 : 0 ≤ Q₀)
    {T : ℝ} (hT : 0 ≤ T) (F : Finset (S → ℕ)) {ε : ℝ} (hε : 0 < ε) :
    ∀ τ, 0 ≤ τ → τ ≤ T → ∀ a : S → ℕ, ∀ G : Finset (S → ℕ), G ⊆ F →
      (∀ b ∈ G, ε ≤ |f b - f a|) →
      ∑ b ∈ G, (N.jumpSystem (N.volumeScale κ V hV)).Pmin τ a b
        ≤ (2 * M * (K + L) + D ^ 2 * V * Q₀) * T / ε ^ 2 := by
  intro τ hτ hτT a G hGF hG
  have hD' : ∀ i a, (N.jumpSystem (N.volumeScale κ V hV)).rate i a ≠ 0 →
      |f ((N.jumpSystem (N.volumeScale κ V hV)).next i a) - f a| ≤ D := by
    intro i a hr
    have hen : N.Enabled a i := by
      refine N.stochasticMassActionRate_ne_zero_imp_Enabled (κ := N.volumeScale κ V hV)
        (n := a) (r := i) ?_
      exact hr
    show |f (N.jumpNextCount a i) - f a| ≤ D
    exact hD i a hen
  have hQ0' : 0 ≤ V * Q₀ := mul_nonneg hV.le hQ0
  have h1 := JumpSystem.fluctuation_sq_le_uniform (N.jumpSystem (N.volumeScale κ V hV))
    f hf0 hfM hM hK hK0 hL hL0 hD' hD0 hQ hQ0' hτ a F
  have h3 : 0 ≤ 2 * M * (K + L) + D ^ 2 * V * Q₀ := by positivity
  have h2 : (2 * M * (K + L) + D ^ 2 * V * Q₀) * τ
      ≤ (2 * M * (K + L) + D ^ 2 * V * Q₀) * T := by
    exact mul_le_mul_of_nonneg_left (by linarith) h3
  have h4 : 0 ≤ (2 * M * (K + L) + D ^ 2 * V * Q₀) * T := mul_nonneg h3 hT
  rw [le_div_iff₀ (sq_pos_of_pos hε)]
  calc (∑ b ∈ G, (N.jumpSystem (N.volumeScale κ V hV)).Pmin τ a b) * ε ^ 2
      = ∑ b ∈ G, (N.jumpSystem (N.volumeScale κ V hV)).Pmin τ a b * ε ^ 2 := by
        rw [Finset.sum_mul]
    _ ≤ ∑ b ∈ G, (N.jumpSystem (N.volumeScale κ V hV)).Pmin τ a b * (f b - f a) ^ 2 := by
        refine Finset.sum_le_sum fun b hb => ?_
        have h5 : ε ^ 2 ≤ (f b - f a) ^ 2 := by
          have h6 : ε ^ 2 ≤ |f b - f a| ^ 2 :=
            (sq_le_sq).2 (by simpa [abs_of_pos hε] using hG b hb)
          have h7 : |f b - f a| ^ 2 = (f b - f a) ^ 2 := sq_abs _
          linarith
        exact mul_le_mul_of_nonneg_left h5
          ((N.jumpSystem (N.volumeScale κ V hV)).Pmin_nonneg τ hτ a b)
    _ ≤ ∑ b ∈ F, (N.jumpSystem (N.volumeScale κ V hV)).Pmin τ a b * (f b - f a) ^ 2 := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hGF fun b _ _ =>
          mul_nonneg ((N.jumpSystem (N.volumeScale κ V hV)).Pmin_nonneg τ hτ a b)
            (sq_nonneg (f b - f a))
    _ ≤ (2 * M * (K + L) + D ^ 2 * V * Q₀) * τ := by
        have hx := h1
        rw [show D ^ 2 * (V * Q₀) = D ^ 2 * V * Q₀ by ring] at hx
        exact hx
    _ ≤ (2 * M * (K + L) + D ^ 2 * V * Q₀) * T := h2


/-- **The link with the repository's uniform-in-time fluctuation concentration.**  The
repository's `CRNT.Network.fluctuation_uniform_concentration` bounds the mass of the
volume-scaled chain which has left the ball around the trajectory point by the *exit mass*
— the law-of-large-numbers scale, of size `O(1/V)`.  The second-moment estimate of this
module bounds, at the *fluctuation scale*, the mass of the chain whose species density
deviates from its initial value by at least `ε`; the two bounds hold simultaneously, and
both are uniform in time within the window.

The constant of the fluctuation-scale bound is `(2 M (K + L) + stoichBound s² Q₀ / V)`, which
is `O(1)` and *independent of the volume* `V = k + 1` up to the `1/V` term: the fluctuation
of the density stays at the fluctuation scale, uniformly in the volume and in the starting
state. -/
theorem fluctuation_uniform_concentration_and_second_moment
    (N : Network S) (κ : RateConstants N) {T Rx δ : ℝ} (hT : 0 < T) (hRx : 0 ≤ Rx)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (x : ℝ → Concentration S) (hxc : ContinuousOn x (Icc 0 T))
    (hx : ∀ t ∈ Ioo 0 T, HasDerivAt x (N.massActionVectorField κ (x t)) t)
    (hxB : ∀ t ∈ Icc 0 T, x t ∈ Icc (0 : Concentration S) fun _ => Rx)
    (n : ℕ → S → ℕ)
    (hn0 : Tendsto (fun k => ∑ s, ((n k s : ℝ) / ((k : ℝ) + 1) - x 0 s) ^ 2) atTop (𝓝 0))
    (s : S) {M K L Q₀ : ℝ} (hM : 0 ≤ M)
    (hfM : ∀ (k : ℕ) (c : S → ℕ), densityObservable ((k : ℝ) + 1) s c ≤ M)
    (hK : ∀ (k : ℕ) (c : S → ℕ),
      (N.jumpSystem (N.volumeScale κ ((k : ℝ) + 1) (by positivity))).drift
        (densityObservable ((k : ℝ) + 1) s) c ≤ K) (hK0 : 0 ≤ K)
    (hL : ∀ (k : ℕ) (c : S → ℕ),
      -L ≤ (N.jumpSystem (N.volumeScale κ ((k : ℝ) + 1) (by positivity))).drift
        (densityObservable ((k : ℝ) + 1) s) c) (hL0 : 0 ≤ L)
    (hQ : ∀ (k : ℕ) (c : S → ℕ),
      (N.jumpSystem (N.volumeScale κ ((k : ℝ) + 1) (by positivity))).q c
        ≤ ((k : ℝ) + 1) * Q₀) (hQ0 : 0 ≤ Q₀)
    {F : Finset (S → ℕ)} {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, 0 < m ∧
      (∀ i < m, ∀ σ ∈ Icc 0 (T / m),
        ∑ s, (x (i * (T / m) + σ) s - x (i * (T / m)) s) ^ 2 ≤ δ ^ 2 / 4) ∧
      (Tendsto (fun k : ℕ => ∑ i ∈ Finset.range m,
          N.windowExitMass κ (V := (k : ℝ) + 1) (by positivity) Rx δ (T / m) x i (n k))
        atTop (𝓝 0)) ∧
      (∀ k : ℕ, ∀ i < m, ∀ c : S → ℕ, ∀ τ ∈ Icc 0 (T / m),
        (∑' b, (if b ∈ ballSet ((k : ℝ) + 1) Rx (x (i * (T / m))) δ then 0 else
            (N.jumpSystem (N.volumeScale κ ((k : ℝ) + 1) (by positivity))).Pmin τ c b))
          ≤ (∑' b, (if b ∈ ballSet ((k : ℝ) + 1) Rx (x (i * (T / m))) δ then 0 else
            ((N.jumpSystem (N.volumeScale κ ((k : ℝ) + 1) (by positivity))).stopOutside
              (ballSet ((k : ℝ) + 1) Rx (x (i * (T / m))) δ)).Pmin (T / m) c b))) ∧
      (∀ k : ℕ, ∀ i < m, ∀ c : S → ℕ, ∀ τ ∈ Icc 0 (T / m), ∀ G : Finset (S → ℕ), G ⊆ F →
        (∀ b ∈ G, ε ≤ |densityObservable ((k : ℝ) + 1) s b
          - densityObservable ((k : ℝ) + 1) s c|) →
        ∑ b ∈ G, (N.jumpSystem (N.volumeScale κ ((k : ℝ) + 1) (by positivity))).Pmin τ c b
          ≤ (2 * M * (K + L) + N.stoichBound s ^ 2 * Q₀ / ((k : ℝ) + 1)) * (T / m) / ε ^ 2) := by
  obtain ⟨m, hm, hmesh, hexit, hbound⟩ :=
    N.fluctuation_uniform_concentration κ hT hRx hδ hδ1 x hxc hx hxB n hn0
  refine ⟨m, hm, hmesh, hexit, hbound, ?_⟩
  intro k i hi c τ hτ G hGF hG
  have hV0 : 0 < (k : ℝ) + 1 := by positivity
  have hD : ∀ r c, N.Enabled c r →
      |densityObservable ((k : ℝ) + 1) s (N.jumpNextCount c r)
        - densityObservable ((k : ℝ) + 1) s c| ≤ N.stoichBound s / ((k : ℝ) + 1) := by
    intro r c hen
    exact N.densityObservable_increment_bound hV0 s c r hen
  have hD0 : 0 ≤ N.stoichBound s / ((k : ℝ) + 1) :=
    div_nonneg (N.stoichBound_nonneg s) hV0.le
  have hf0 : ∀ c : S → ℕ, 0 ≤ densityObservable ((k : ℝ) + 1) s c :=
    fun c => div_nonneg (Nat.cast_nonneg _) hV0.le
  have h1 := N.fluctuation_uniform_concentration_of_second_moment_uniform_in_time κ hV0
    (densityObservable ((k : ℝ) + 1) s) hf0 (hfM k) hM (hK k) hK0 (hL k) hL0 hD hD0 (hQ k) hQ0
    (T := T / m) (by positivity) F hε τ hτ.1 hτ.2 c G hGF hG
  have hV0ne : ((k : ℝ) + 1) ≠ 0 := hV0.ne'
  have h2' : (N.stoichBound s / ((k : ℝ) + 1)) ^ 2 * ((k : ℝ) + 1) * Q₀
      = N.stoichBound s ^ 2 * Q₀ / ((k : ℝ) + 1) := by
    field_simp
  have h2 : (2 * M * (K + L) + (N.stoichBound s / ((k : ℝ) + 1)) ^ 2 * ((k : ℝ) + 1) * Q₀)
      * (T / m) / ε ^ 2
      = (2 * M * (K + L) + N.stoichBound s ^ 2 * Q₀ / ((k : ℝ) + 1)) * (T / m) / ε ^ 2 := by
    rw [h2']
  rw [h2] at h1
  exact h1


end Network
end CRNT

/-! ## The bounded versus the unbounded case -/

namespace CRNT
namespace JumpSystem

/-! ## A concrete instance -/

/-- **The drift of the indicator of the two-state system is nonnegative.** -/
theorem drift_indTrue_nonneg (lam : ℝ) (hlam : 0 ≤ lam) (b : Bool) :
    0 ≤ (twoState lam hlam).drift indTrue b := by
  rw [drift_indTrue lam hlam b]
  split_ifs <;> positivity

/-- **The increment of the indicator of the two-state system is at most one.** -/
theorem indTrue_increment (lam : ℝ) (hlam : 0 ≤ lam) (i : Unit) (b : Bool) :
    |indTrue ((twoState lam hlam).next i b) - indTrue b| ≤ 1 := by
  simp [twoState, indTrue]
  split_ifs <;> norm_num

/-- **The exit rate of the two-state system is bounded by its rate.** -/
theorem twoState_q_le (lam : ℝ) (hlam : 0 ≤ lam) (b : Bool) : (twoState lam hlam).q b ≤ lam := by
  have hq' : (twoState lam hlam).q b = if b then 0 else lam := by
    show (∑ i : Unit, (twoState lam hlam).rate i b) = if b then 0 else lam
    simp [twoState]
  rw [hq']
  by_cases hb : b
  · simp [hb, hlam]
  · simp [hb]

/-- **A concrete instance: the fluctuation-scale estimate for the two-state system.**  The
two-state system `false → true` at rate `lam`, with the observable `1_{true}`: the
fluctuation of the observable about its initial value satisfies

  `∑_{b ∈ {false, true}} Pmin(T)(false, b) · (1_{true} b − 1_{true} false)² ≤ 3 lam T`,

the same constant as the second-moment estimate `CRNT.JumpSystem.secondMoment_indTrue`,
but now in the uniform-in-the-starting-state form. -/
theorem fluctuation_sq_le_uniform_indTrue (lam : ℝ) (hlam : 0 ≤ lam) {T : ℝ} (hT : 0 ≤ T) :
    ∑ b ∈ ({false, true} : Finset Bool), (twoState lam hlam).Pmin T false b
      * (indTrue b - indTrue false) ^ 2 ≤ (2 * 1 * (lam + 0) + 1 ^ 2 * lam) * T := by
  have hV : ∀ b : Bool, 0 ≤ indTrue b := by
    intro b
    by_cases hb : b <;> simp [indTrue, hb]
  have hV' : ∀ b : Bool, indTrue b ≤ 1 := by
    intro b
    by_cases hb : b <;> simp [indTrue, hb]
  have hK : ∀ b : Bool, (twoState lam hlam).drift indTrue b ≤ lam := by
    intro b
    rw [drift_indTrue lam hlam b]
    split_ifs <;> linarith
  have hL : ∀ b : Bool, -0 ≤ (twoState lam hlam).drift indTrue b := by
    intro b
    rw [neg_zero]
    exact drift_indTrue_nonneg lam hlam b
  have hD : ∀ i : Unit, ∀ b : Bool, (twoState lam hlam).rate i b ≠ 0 →
      |indTrue ((twoState lam hlam).next i b) - indTrue b| ≤ 1 :=
    fun _ _ _ => indTrue_increment lam hlam _ _
  have hQ : ∀ b : Bool, (twoState lam hlam).q b ≤ lam := twoState_q_le lam hlam
  exact CRNT.JumpSystem.fluctuation_sq_le_uniform (twoState lam hlam) indTrue (M := 1) (K := lam) (L := 0) (D := 1) (Q := lam)
    hV hV' (by norm_num) hK hlam hL (by norm_num) hD (by norm_num) hQ hlam hT false
    ({false, true} : Finset Bool)

/-- **The exact degradation: an unbounded observable has an unbounded second-moment
constant.**  In the two-state system `false → true` at rate `lam`, the drift of the square of
the observable `n · 1_{true}` at `false` is `lam · n²`.  Hence a hypothesis
`drift(V²) ≤ C` forces `C ≥ lam n²`: for an unbounded observable the constant of the
fluctuation estimate cannot be chosen independently of the observable, and the uniform
constant `2 M (K + L) + D² Q` of the bounded case — the `O(1)` constant of the
fluctuation-scale estimate — is replaced by the `O(T)` bound `4 V(a)² + 2 C T` of
`CRNT.JumpSystem.fluctuation_sq_le_uniform_unbounded`, whose `T`-coefficient `2 C` is not
controlled by the drift of `V` at all. -/
theorem drift_sq_twoState_scaled (lam : ℝ) (hlam : 0 ≤ lam) (n : ℝ) :
    (twoState lam hlam).drift (fun b => (n * indTrue b) ^ 2) false = lam * n ^ 2 := by
  have hq : (twoState lam hlam).rate (Unit.unit) false = lam := by
    show (if false then 0 else lam) = lam
    simp
  have hn : (twoState lam hlam).next (Unit.unit) false = true := by
    show !false = true
    simp
  show (∑ i : Unit, (twoState lam hlam).rate i false *
      ((n * indTrue ((twoState lam hlam).next i false)) ^ 2
        - (n * indTrue false) ^ 2)) = lam * n ^ 2
  have : (∑ i : Unit, (twoState lam hlam).rate i false *
      ((n * indTrue ((twoState lam hlam).next i false)) ^ 2
        - (n * indTrue false) ^ 2))
      = (twoState lam hlam).rate (Unit.unit) false *
        ((n * indTrue ((twoState lam hlam).next (Unit.unit) false)) ^ 2
          - (n * indTrue false) ^ 2) := by
    simp
  rw [this, hq, hn]
  simp [indTrue]

end JumpSystem
end CRNT

/-! ## Axioms -/

#print axioms CRNT.JumpSystem.drift_sq_le_inc
#print axioms CRNT.JumpSystem.drift_sq_sub_le
#print axioms CRNT.JumpSystem.drift_div
#print axioms CRNT.JumpSystem.fluctuation_sq_le_uniform
#print axioms CRNT.JumpSystem.fluctuation_sq_le_uniform_of_bounded
#print axioms CRNT.JumpSystem.fluctuation_sq_le_uniform_in_time
#print axioms CRNT.JumpSystem.fluctuation_sq_le_uniform_scaled
#print axioms CRNT.JumpSystem.fluctuation_chebyshev_uniform
#print axioms CRNT.JumpSystem.fluctuation_chebyshev_uniform_scaled
#print axioms CRNT.JumpSystem.fluctuation_sq_le_uniform_unbounded
#print axioms CRNT.JumpSystem.fluctuation_sq_le_uniform_indTrue
#print axioms CRNT.JumpSystem.drift_sq_twoState_scaled
#print axioms CRNT.Network.jumpSystem_q_volumeScale
#print axioms CRNT.Network.stoichBound_le
#print axioms CRNT.Network.densityObservable_jumpNextCount_sub
#print axioms CRNT.Network.densityObservable_increment_bound
#print axioms CRNT.Network.fluctuation_uniform_concentration_of_second_moment
#print axioms CRNT.Network.fluctuation_uniform_concentration_of_second_moment_uniform_in_time
#print axioms CRNT.Network.fluctuation_uniform_concentration_and_second_moment
