import CRNT.Design.AntitheticFoster

/-!
# An exponential-drift Lyapunov function for the antithetic closed loop: the candidate, and the
obstruction

This module closes, for leaf **C3** ("antithetic integral feedback") of `docs/field-map.md`, the
item left open by `CRNT.Design.AntitheticFoster`: the **geometric ergodicity** of the antithetic
closed loop `CRNT.Antithetic.closedLoop`.

## 1. The controller and the criterion

The antithetic integral controller of Briat, Gupta and Khammash (*Antithetic integral feedback
ensures robust perfect adaptation in noisy biomolecular networks*, Cell Systems 2 (2016); *Robustness
analysis of a class of antithetic integral controllers*, Automatica (2019)) pairs a **reference**
reaction with a **sensing** reaction acting on the plant with opposite signs: the *charge*
`q = z₁ − z₂` (the integral of the control error) is the difference of the two.  In the molecular
realization of the repository the anti-correlation is realized by an **annihilation**
`Z₁ + Z₂ → ∅` between the actuated species `Z₁` and the sensing species `Z₂`, while the reference
reaction `∅ → Z₁` feeds `Z₁` without bound.  On the species `0 = Z₁`, `1 = Z₂`, `2 = X` the five
reactions are

```text
0 : ∅ → Z₁        (reference,   rate μ)
1 : Z₁ + Z₂ → ∅   (annihilation, rate η)
2 : Z₁ → Z₁ + X   (actuation,   rate k)
3 : X → ∅         (degradation,  rate γ)
4 : X → X + Z₂    (sensing,     rate θ)
```

The **geometric (V-uniform) ergodicity** criterion of Meyn and Tweedie (*Markov Chains and
Stochastic Stability*, Cambridge University Press, 1993; Chapter 16) says: on an irreducible
countable-state chain, a nonnegative Lyapunov function `W` with **finite sublevel sets** and an
**exponential drift** `QW ≤ −c W + K` (`c > 0`, `K ≥ 0`) makes the chain geometrically ergodic.
The repository packages the criterion in
`CRNT.Stochastic.FosterLyapunovCertificate.geometric_ergodic_of_exponential_drift` (which also
needs a Foster certificate, to make the minimal transition function stochastic) and instantiates it
at the antithetic closed loop in
`CRNT.Antithetic.closedLoop_geometric_ergodic_of_exponential_drift`.

## 2. What the repository already contains

* the **piecewise quadratic** Lyapunov function `CRNT.AntitheticErgodic.lyap`
  `= φ(q) + c_b x² − c_c x q + c_d z₁ z₂` with `φ(q) = c_A q²` (`q ≥ 0`), `c_B q²` (`q < 0`),
  its **exact drift** `drift_lyap` and its Foster drift bound `drift_lyap_le`
  (`Q lyap ≤ −fLyap + cK` with the norm-like function `fLyap`);
* the **modified (continuous) function** `CRNT.AntitheticMeanOutput.wLyap` (equal to `lyap` on the
  region `z₂ ≤ z₁` and to `c_b x² + c_d z₁²` above it), its exponential drift bound
  `drift_wLyap_le`, and the uniform second moment `output_sq_moment_le`;
* the **Foster certificate** `CRNT.Antithetic.closedLoop_fosterCertificate` and the general
  theorem `CRNT.Stochastic.FosterLyapunovCertificate.geometric_ergodic_of_exponential_drift`
  (`CRNT.Design.AntitheticFoster`);
* the two **obstructions** already proved there: `CRNT.Antithetic.lyap_no_exponential_drift`
  (on the line `z₁ = 0`, `lyap` grows *quadratically* in `z₂` while its drift grows only
  *linearly*, so `Q lyap + c · lyap → +∞` for every `c > 0`) and
  `CRNT.Antithetic.wLyap_sublevel_infinite` (on the region `z₁ < z₂`, `wLyap` does not depend on
  `z₂` at all, so its sublevel sets are infinite).

## 3. What this module adds

1. `CRNT.Antithetic.wLyapFamily`: the **family of candidates** — on the region `z₂ ≤ z₁` the
   piecewise quadratic `lyap` of the repository, on the region `z₁ < z₂` the quadratic
   `α x² + β z₁² + δ (z₂ − z₁) + e (z₂ − z₁)²`.  The candidate named by the campaign,
   `CRNT.Antithetic.wLyap2`, is the member `α = c_b`, `β = c_d`, `δ = c_d`, `e = 0`: it is
   `lyap` on the region `z₂ ≤ z₁` and `c_b x² + c_d z₁² + c_d (z₂ − z₁)` above it.
2. `CRNT.Antithetic.wLyap2_finite`: **the candidate does have finite sublevel sets.**  This is the
   crux of the campaign's question: a function that *grows* in `z₂` has infinite sublevel sets, but
   the candidate grows in `z₂` only *together with* `z₁` (the term `c_d (z₂ − z₁)` is zero on the
   line `z₂ = z₁` and positive above it), and the sublevel sets are finite.
3. `CRNT.Antithetic.wLyap2_le_lyap` and `CRNT.Antithetic.drift_wLyap2_le_regionA`: the candidate is
   dominated by the piecewise quadratic `lyap` of the repository, and on the region `z₂ ≤ z₁` it
   has the Foster drift of `lyap` (`Q wLyap2 ≤ −fLyap + cK`).  The obstruction below is therefore
   *localized* to the region `z₁ < z₂`, and in particular to the line `z₁ = 0`.
3. `CRNT.Antithetic.drift_wLyapFamily_at`: the **exact drift** of the family on the line `z₁ = 0`,
   at the count `(0, m, 1)`.
4. `CRNT.Antithetic.wLyapFamily_no_exponential_drift`: **the obstruction.**  No member of the
   family with `δ > 0` (a positive `z₂`-slope) and `e ≥ 0` (a nonnegative `z₂²`-coefficient) has
   an exponential drift: the drift on the line `z₁ = 0` is *bounded* while the function itself
   grows like `δ m + e m²` there.
5. `CRNT.Antithetic.wLyap2_no_exponentialDriftCertificate`: the candidate carries no exponential
   drift certificate, so `CRNT.Antithetic.closedLoop_geometric_ergodic_of_exponential_drift` cannot
   be applied with `W = wLyap2`, and the geometric ergodicity of the closed loop is **not**
   established by it.
6. `CRNT.Antithetic.wLyapSlope`: the **sharpest obstruction** — the family of functions which are
   *affine in `z₂`* on the region `z₁ < z₂`, with a slope `s (z₁)` that depends on `z₁` but not on
   `x` (the most general shape of the candidates of the campaign), and
   `CRNT.Antithetic.wLyapSlope_no_exponential_drift`: **no** member of that family with a positive
   slope on the line `z₁ = 0` carries an exponential drift.  The positive slope is *necessary* for
   the finite sublevel sets, so the whole class is excluded.

## 4. The obstruction, in detail

On the line `z₁ = 0` the annihilation is *disabled* (its rate is `η z₁ z₂ = 0`), so the counts
`(0, m, x)` are fed only by the reference reaction `∅ → Z₁` (rate `μ`), the degradation `X → ∅`
(rate `γ x`) and the sensing `X → X + Z₂` (rate `θ x`).  For the family,

```text
W(0, m, 1)  = α + δ m + e m²
Q W(0, m, 1) = μ (β − δ + e − 2 e m) − γ α + θ (δ + e (2 m + 1)),
```

so the drift is *affine* in `m` while `W` itself is *quadratic* in `m`: for every `c > 0` the
quantity `Q W + c W` is unbounded above on the line `z₁ = 0` (`wLyapFamily_no_exponential_drift`).
The mechanism is the one recorded in `CRNT.Design.AntitheticFoster`: on the line `z₁ = 0` the
sensing direction `z₂ ↦ z₂ + 1` contributes `+ θ δ > 0` to the drift and *nothing* compensates it,
because the reference reaction `∅ → Z₁` changes `z₁`, not `z₂`, and the annihilation — the only
consumer of `z₂` — is switched off there.

`wLyapSlope_no_exponential_drift` makes this into a *sharp* statement, by allowing the slope in
`z₂` to depend on `z₁` (but not on `x`): for

```text
W(k, m, x) = α x² + β k² + s (k) (m − k)          (region k = z₁ < z₂ = m)
```

the two drift conditions are contradictory.

* On the line `z₁ = 0` (`drift_wLyapSlope_zero`):
  `Q W(0, m, 1) = μ (s 1 − s 0) m + μ (β − s 1) − γ α + θ s 0`, and `W(0, m, 1) = α + s 0 m`.
  Since `Q W + c W` is bounded above on the half line `m ≥ 2`, its slope must be nonpositive:
  `μ (s 1 − s 0) + c s 0 ≤ 0`.  As `c s 0 > 0`, the slope in `z₂` must **drop** from `z₁ = 0` to
  `z₁ = 1`.
* On the line `z₁ = 1` (`drift_wLyapSlope_one`) the annihilation is active, with rate `η z₂`, and
  contributes `η m (W(0, m − 1, 1) − W(1, m, 1))`, whose leading coefficient in `m` is
  `η (s 0 − s 1)`.  Since `Q W + c W` is bounded above on the half line `m ≥ 3` and `W(1, m, 1)`
  is affine in `m`, that leading coefficient must be nonpositive: `η (s 0 − s 1) ≤ 0`, i.e. the
  slope in `z₂` must **not** drop.

The two requirements contradict each other (`μ (s 1 − s 0) + c s 0 ≤ 0` with `s 1 ≥ s 0` and
`c s 0 > 0`), and this is the obstruction: the two-line argument shows that *no* function of the
shape of the candidates can carry an exponential drift.

## 5. What remains open

* The **geometric ergodicity of the antithetic closed loop is not proved.**  It would require a
  Lyapunov function with finite sublevel sets and an exponential drift; the two functions of the
  repository are excluded by `lyap_no_exponential_drift` and `wLyap_sublevel_infinite`, and the
  whole family of candidates of this module — every function which is affine or quadratic in
  `z₂` on the region `z₁ < z₂`, with a positive `z₂`-slope or a positive `z₂²`-coefficient — is
  excluded by `wLyapFamily_no_exponential_drift` and `wLyapSlope_no_exponential_drift`.
* A successful `W` would have to *decrease* in `z₂` along the line `z₁ = 0` in a way that keeps the
  sublevel sets finite, i.e. it must be genuinely non-polynomial on the region `z₁ < z₂`; the
  exponential-drift condition then has to be checked against the *full* (not polynomial) drift.
  The two-line argument of `wLyapSlope_no_exponential_drift` shows that the `z₂`-slope may not
  decrease either, so such a `W` would have to be non-affine in `z₂` on the region `z₁ < z₂` as
  well (for instance, growing like `z₂^p` with `p` growing with `z₁`).

Depends on: `CRNT.Design.AntitheticFoster` (hence `CRNT.Design.AntitheticErgodic`,
`CRNT.Design.AntitheticMeanOutput`).
-/

open Filter
open scoped BigOperators Topology

namespace CRNT
namespace Antithetic

open Network

variable (κ : closedLoop.RateConstants)

/-- The count `(a, b, c)` read off the three coordinates. -/
theorem mk3_zero (a b c : ℕ) : (mk3 a b c : Fin 3 → ℕ) 0 = a := by simp [mk3]
theorem mk3_one (a b c : ℕ) : (mk3 a b c : Fin 3 → ℕ) 1 = b := by simp [mk3]
theorem mk3_two (a b c : ℕ) : (mk3 a b c : Fin 3 → ℕ) 2 = c := by simp [mk3]

/-- The coefficient `c_b` is positive. -/
theorem cb_pos : 0 < cb κ := by
  unfold cb θ
  have := κ.positive (4 : Fin 5)
  positivity

/-- The coefficient `c_d` is positive. -/
theorem cd_pos : 0 < cd κ := by
  unfold cd γ
  have := κ.positive (3 : Fin 5)
  positivity

/-- The coefficient `c_c` is nonnegative. -/
theorem cc_nonneg : 0 ≤ cc κ := by
  unfold cc γ θ
  have := κ.positive (3 : Fin 5)
  have := κ.positive (4 : Fin 5)
  positivity

/-- **The family of candidates for an exponential drift.**  On the region `z₂ ≤ z₁` the function is
the piecewise quadratic `lyap` of the repository; on the region `z₁ < z₂` it is the quadratic
`α x² + β z₁² + δ (z₂ − z₁) + e (z₂ − z₁)²`.  The parameter `δ` is the *slope* of the function in
`z₂` above the line `z₂ = z₁`, and `e` its quadratic coefficient. -/
noncomputable def wLyapFamily (κ : closedLoop.RateConstants) (α β δ e : ℝ)
    (n : Fin 3 → ℕ) : ℝ :=
  if n 1 ≤ n 0 then lyap κ n
  else α * (n 2 : ℝ) ^ 2 + β * (n 0 : ℝ) ^ 2 + δ * ((n 1 : ℝ) - (n 0 : ℝ)) +
    e * ((n 1 : ℝ) - (n 0 : ℝ)) ^ 2

/-- On the region `z₂ ≤ z₁` the family is the piecewise quadratic `lyap`. -/
theorem wLyapFamily_of_le {n : Fin 3 → ℕ} (h : n 1 ≤ n 0) :
    wLyapFamily κ α β δ e n = lyap κ n := by
  unfold wLyapFamily
  rw [if_pos h]

/-- On the region `z₁ < z₂` the family is the quadratic `α x² + β z₁² + δ (z₂ − z₁) + e (z₂ − z₁)²`. -/
theorem wLyapFamily_of_lt {n : Fin 3 → ℕ} (h : n 0 < n 1) :
    wLyapFamily κ α β δ e n = α * (n 2 : ℝ) ^ 2 + β * (n 0 : ℝ) ^ 2 +
      δ * ((n 1 : ℝ) - (n 0 : ℝ)) + e * ((n 1 : ℝ) - (n 0 : ℝ)) ^ 2 := by
  unfold wLyapFamily
  rw [if_neg (by omega)]

/-- **The candidate Lyapunov function with an exponential drift.**  It is the piecewise quadratic
`lyap` on the region `z₂ ≤ z₁` and the quadratic `c_b x² + c_d z₁² + c_d (z₂ − z₁)` on the region
`z₁ < z₂`; the additional term `c_d (z₂ − z₁)` makes the function grow in `z₂` above the line
`z₂ = z₁`, and vanishes on that line, so the two pieces agree there. -/
noncomputable def wLyap2 (κ : closedLoop.RateConstants) (n : Fin 3 → ℕ) : ℝ :=
  wLyapFamily κ (cb κ) (cd κ) (cd κ) 0 n

theorem wLyap2_of_le {n : Fin 3 → ℕ} (h : n 1 ≤ n 0) : wLyap2 κ n = lyap κ n := by
  simp [wLyap2, wLyapFamily_of_le κ h]

theorem wLyap2_of_lt {n : Fin 3 → ℕ} (h : n 0 < n 1) :
    wLyap2 κ n = cb κ * (n 2 : ℝ) ^ 2 + cd κ * (n 0 : ℝ) ^ 2 +
      cd κ * ((n 1 : ℝ) - (n 0 : ℝ)) := by
  simp [wLyap2, wLyapFamily_of_lt κ h]

/-- **The candidate is nonnegative.** -/
theorem wLyap2_nonneg (n : Fin 3 → ℕ) : 0 ≤ wLyap2 κ n := by
  by_cases h : n 1 ≤ n 0
  · rw [wLyap2_of_le κ h]
    exact lyap_nonneg κ n
  · have hlt : n 0 < n 1 := by omega
    rw [wLyap2_of_lt κ hlt]
    have hb : 0 ≤ cb κ := (cb_pos κ).le
    have hd : 0 ≤ cd κ := (cd_pos κ).le
    have hq : 0 ≤ (n 1 : ℝ) - (n 0 : ℝ) := by
      have : (n 0 : ℝ) < (n 1 : ℝ) := by exact_mod_cast hlt
      linarith
    positivity

/-- `c_B = 2 c_d`. -/
theorem cB_eq_two_cd : cB κ = 2 * cd κ := by unfold cB cd; ring

/-- **The candidate is dominated by the piecewise quadratic `lyap`.**  On the region `z₁ < z₂` the
difference is `(z₂ − z₁) (c_B (z₂ − z₁) + c_c x + c_d z₁ − c_d)`, which is nonnegative because
`c_B = 2 c_d` and `z₂ − z₁ ≥ 1`. -/
theorem wLyap2_le_lyap (n : Fin 3 → ℕ) : wLyap2 κ n ≤ lyap κ n := by
  by_cases h : n 1 ≤ n 0
  · rw [wLyap2_of_le κ h]
  · have hlt : n 0 < n 1 := by omega
    rw [wLyap2_of_lt κ hlt]
    set p : ℝ := (n 1 : ℝ) - (n 0 : ℝ) with hpdef
    have hq : (n 0 : ℝ) - (n 1 : ℝ) = -p := by simp only [hpdef]; ring
    have hphi : phi κ (n 0) (n 1) = cB κ * p ^ 2 := by
      unfold phi
      rw [if_neg (by omega)]
      rw [hq]
      ring
    have hp : 1 ≤ p := by
      have h1 : (n 0 : ℝ) + 1 ≤ (n 1 : ℝ) := by exact_mod_cast (by omega)
      rw [hpdef]
      linarith
    have hz2 : (n 1 : ℝ) = (n 0 : ℝ) + p := by simp only [hpdef]; ring
    have hB : 0 ≤ cB κ := by unfold cB; positivity
    have hd : 0 ≤ cd κ := (cd_pos κ).le
    have hcc : 0 ≤ cc κ := cc_nonneg κ
    have hZ1 : 0 ≤ (n 0 : ℝ) := Nat.cast_nonneg _
    have hX : 0 ≤ (n 2 : ℝ) := Nat.cast_nonneg _
    rw [lyap, hphi]
    rw [hq, hz2]
    have hprod : 0 ≤ p * (cB κ * p - cd κ) := by
      refine mul_nonneg (by nlinarith) ?_
      have hcB : cB κ = 2 * cd κ := cB_eq_two_cd κ
      nlinarith [hp, hB, hd]
    have hXp : 0 ≤ cc κ * (n 2 : ℝ) * p := mul_nonneg (mul_nonneg hcc hX) (by nlinarith)
    have hZ1p : 0 ≤ cd κ * (n 0 : ℝ) * p := mul_nonneg (mul_nonneg hd hZ1) (by nlinarith)
    nlinarith [hprod, hXp, hZ1p]

/-- **On the region `z₂ ≤ z₁` the candidate has the Foster drift of the piecewise quadratic
`lyap`.**  Indeed the candidate agrees with `lyap` there and is dominated by `lyap` everywhere
(`wLyap2_le_lyap`), so the drift of the candidate is at most the drift of `lyap`, which is bounded
by `−fLyap + cK` (`drift_lyap_le`).  The obstruction of this module is therefore *localized* to the
region `z₁ < z₂`, and in particular to the line `z₁ = 0`. -/
theorem drift_wLyap2_le_regionA {n : Fin 3 → ℕ} (h : n 1 ≤ n 0) :
    (closedLoop.jumpSystem κ).drift (wLyap2 κ) n ≤ -fLyap κ n + cK κ := by
  have hWn : wLyap2 κ n = lyap κ n := wLyap2_of_le κ h
  have hdr : (closedLoop.jumpSystem κ).drift (wLyap2 κ) n ≤
      (closedLoop.jumpSystem κ).drift (lyap κ) n := by
    unfold JumpSystem.drift
    refine Finset.sum_le_sum fun r _ => ?_
    refine mul_le_mul_of_nonneg_left ?_ ((closedLoop.jumpSystem κ).rate_nonneg r n)
    rw [hWn]
    linarith [wLyap2_le_lyap κ ((closedLoop.jumpSystem κ).next r n)]
  have h1 := drift_lyap_le κ n
  linarith

/-- **The candidate has finite sublevel sets.**  On the region `z₂ ≤ z₁` this is the finiteness of
the sublevel sets of `lyap` (`lyap_finite`); on the region `z₁ < z₂` the term `c_d (z₂ − z₁)`
bounds `z₂` in terms of `z₁`, and the quadratic terms bound `z₁` and `x`. -/
theorem wLyap2_finite (R : ℝ) : {n | wLyap2 κ n ≤ R}.Finite := by
  by_cases hR : 0 ≤ R
  · have hb : 0 < cb κ := cb_pos κ
    have hd : 0 < cd κ := cd_pos κ
    have hA : {n | wLyap2 κ n ≤ R ∧ n 1 ≤ n 0}.Finite := by
      refine (lyap_finite κ R).subset fun n hn => ?_
      simpa [wLyap2_of_le κ hn.2] using hn.1
    have hB : {n | wLyap2 κ n ≤ R ∧ n 0 < n 1}.Finite := by
      set B := max (R / cb κ) (2 * (R / cd κ)) with hBdef
      refine finite_of_bounds B _ fun n hn => ?_
      have hW := hn.1
      rw [wLyap2_of_lt κ hn.2] at hW
      have hnonneg : 0 ≤ cd κ * ((n 1 : ℝ) - (n 0 : ℝ)) := by
        have h1 : 0 ≤ (n 1 : ℝ) - (n 0 : ℝ) := by
          have h2 : (n 0 : ℝ) < (n 1 : ℝ) := by exact_mod_cast hn.2
          linarith
        positivity
      have h1 : cb κ * (n 2 : ℝ) ^ 2 ≤ R := by nlinarith
      have h2 : cd κ * (n 0 : ℝ) ^ 2 ≤ R := by nlinarith
      have h3 : cd κ * ((n 1 : ℝ) - (n 0 : ℝ)) ≤ R := by nlinarith
      have hx : (n 2 : ℝ) ≤ R / cb κ := by
        rw [le_div_iff₀ hb]
        have := cast_le_sq (n 2)
        nlinarith
      have hz1 : (n 0 : ℝ) ≤ R / cd κ := by
        rw [le_div_iff₀ hd]
        have := cast_le_sq (n 0)
        nlinarith
      have hcdZ1 : cd κ * (n 0 : ℝ) ≤ cd κ * (n 0 : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left (cast_le_sq (n 0)) hd.le
      have hcdZ1' : cd κ * (n 0 : ℝ) ≤ R := le_trans hcdZ1 h2
      have hz2 : (n 1 : ℝ) ≤ 2 * (R / cd κ) := by
        have heq : (2 * R) / cd κ = 2 * (R / cd κ) := by ring
        have hsum : cd κ * (n 1 : ℝ) ≤ 2 * R := by
          have heq2 : cd κ * (n 1 : ℝ) =
              cd κ * ((n 1 : ℝ) - (n 0 : ℝ)) + cd κ * (n 0 : ℝ) := by ring
          rw [heq2]
          linarith
        rw [← heq, le_div_iff₀ hd]
        nlinarith
      have hRcb : R / cb κ ≤ B := by
        rw [hBdef]; exact le_max_left _ _
      have hRcd2 : 2 * (R / cd κ) ≤ B := by
        rw [hBdef]; exact le_max_right _ _
      have hRcd0 : 0 ≤ R / cd κ := div_nonneg hR hd.le
      refine ⟨by linarith, by linarith, by linarith⟩
    have hAB : ({n | wLyap2 κ n ≤ R ∧ n 1 ≤ n 0} ∪ {n | wLyap2 κ n ≤ R ∧ n 0 < n 1}).Finite :=
      Set.finite_union.mpr ⟨hA, hB⟩
    refine hAB.subset fun n hn => ?_
    by_cases h : n 1 ≤ n 0
    · exact Or.inl ⟨hn, h⟩
    · exact Or.inr ⟨hn, by omega⟩
  · have hempty : {n | wLyap2 κ n ≤ R} = ∅ := by
      ext n
      simp only [Set.mem_setOf_eq]
      constructor
      · intro h
        have h2 := le_trans (wLyap2_nonneg κ n) h
        linarith
      · intro h
        simp at h
    rw [hempty]
    exact Set.finite_empty

/-- **The exact drift of the family on the line `z₁ = 0`.**  At the count `(0, m, 1)` (with `m ≥ 2`)
the annihilation and the actuation are disabled, so only the reference, the degradation and the
sensing contribute; the drift is *affine* in `m`, while the function itself is *quadratic* in `m`. -/
theorem drift_wLyapFamily_at (κ : closedLoop.RateConstants) (α β δ e : ℝ) (m : ℕ) (hm : 2 ≤ m) :
    (closedLoop.jumpSystem κ).drift (wLyapFamily κ α β δ e) (mk3 0 m 1) =
      μ κ * (β - δ) + 2 * e * (θ κ - μ κ) * (m : ℝ) +
        (μ κ * e - γ κ * α + θ κ * δ + θ κ * e) := by
  obtain ⟨r0, r1, r2, r3, r4⟩ := rate_eq κ (mk3 0 m 1)
  show ∑ r : closedLoop.R, closedLoop.stochasticMassActionRate κ (mk3 0 m 1) r *
      (wLyapFamily κ α β δ e (closedLoop.jumpNextCount (mk3 0 m 1) r) -
        wLyapFamily κ α β δ e (mk3 0 m 1)) = _
  change ∑ r : Fin 5, _ = _
  rw [Fin.sum_univ_five]
  have hnext0 : closedLoop.jumpNextCount (mk3 0 m 1) (0 : Fin 5) = mk3 1 m 1 := by
    funext i; fin_cases i <;> simp [jumpNextCount, closedLoop, rxn, mk3]
  have hnext1 : closedLoop.jumpNextCount (mk3 0 m 1) (1 : Fin 5) = mk3 0 (m - 1) 1 := by
    funext i; fin_cases i <;> simp [jumpNextCount, closedLoop, rxn, mk3]
  have hnext3 : closedLoop.jumpNextCount (mk3 0 m 1) (3 : Fin 5) = mk3 0 m 0 := by
    funext i; fin_cases i <;> simp [jumpNextCount, closedLoop, rxn, mk3]
  have hnext4 : closedLoop.jumpNextCount (mk3 0 m 1) (4 : Fin 5) = mk3 0 (m + 1) 1 := by
    funext i; fin_cases i <;> simp [jumpNextCount, closedLoop, rxn, mk3]
  have hA : (mk3 1 m 1 : Fin 3 → ℕ) 0 < (mk3 1 m 1 : Fin 3 → ℕ) 1 := by
    rw [mk3_zero, mk3_one]; omega
  have hB : (mk3 0 m 1 : Fin 3 → ℕ) 0 < (mk3 0 m 1 : Fin 3 → ℕ) 1 := by
    rw [mk3_zero, mk3_one]; omega
  have hD : (mk3 0 m 0 : Fin 3 → ℕ) 0 < (mk3 0 m 0 : Fin 3 → ℕ) 1 := by
    rw [mk3_zero, mk3_one]; omega
  have hE : (mk3 0 (m + 1) 1 : Fin 3 → ℕ) 0 < (mk3 0 (m + 1) 1 : Fin 3 → ℕ) 1 := by
    rw [mk3_zero, mk3_one]; omega
  have t0 : closedLoop.stochasticMassActionRate κ (mk3 0 m 1) (0 : Fin 5) *
        (wLyapFamily κ α β δ e (closedLoop.jumpNextCount (mk3 0 m 1) (0 : Fin 5)) -
          wLyapFamily κ α β δ e (mk3 0 m 1)) = μ κ * (β - δ + e - 2 * e * (m : ℝ)) := by
    rw [r0, hnext0, wLyapFamily_of_lt κ hA, wLyapFamily_of_lt κ hB]
    simp only [mk3_zero, mk3_one, mk3_two]
    push_cast; ring
  have t1 : closedLoop.stochasticMassActionRate κ (mk3 0 m 1) (1 : Fin 5) *
        (wLyapFamily κ α β δ e (closedLoop.jumpNextCount (mk3 0 m 1) (1 : Fin 5)) -
          wLyapFamily κ α β δ e (mk3 0 m 1)) = 0 := by
    rw [r1]
    simp only [mk3_zero]
    push_cast
    ring
  have t2 : closedLoop.stochasticMassActionRate κ (mk3 0 m 1) (2 : Fin 5) *
        (wLyapFamily κ α β δ e (closedLoop.jumpNextCount (mk3 0 m 1) (2 : Fin 5)) -
          wLyapFamily κ α β δ e (mk3 0 m 1)) = 0 := by
    rw [r2]
    simp only [mk3_zero]
    push_cast
    ring
  have t3 : closedLoop.stochasticMassActionRate κ (mk3 0 m 1) (3 : Fin 5) *
        (wLyapFamily κ α β δ e (closedLoop.jumpNextCount (mk3 0 m 1) (3 : Fin 5)) -
          wLyapFamily κ α β δ e (mk3 0 m 1)) = γ κ * (-α) := by
    rw [r3, hnext3, wLyapFamily_of_lt κ hD, wLyapFamily_of_lt κ hB]
    simp only [mk3_zero, mk3_one, mk3_two]
    push_cast; ring
  have t4 : closedLoop.stochasticMassActionRate κ (mk3 0 m 1) (4 : Fin 5) *
        (wLyapFamily κ α β δ e (closedLoop.jumpNextCount (mk3 0 m 1) (4 : Fin 5)) -
          wLyapFamily κ α β δ e (mk3 0 m 1)) = θ κ * δ + 2 * θ κ * e * (m : ℝ) + θ κ * e := by
    rw [r4, hnext4, wLyapFamily_of_lt κ hE, wLyapFamily_of_lt κ hB]
    simp only [mk3_zero, mk3_one, mk3_two]
    push_cast; ring
  rw [t0, t1, t2, t3, t4]
  ring

/-- **The obstruction: no member of the family with a positive `z₂`-slope and a nonnegative
`z₂²`-coefficient has an exponential drift.**  On the line `z₁ = 0` the annihilation is disabled,
the drift of the family is *affine* in `z₂` (see `drift_wLyapFamily_at`) while the family itself
grows like `δ z₂ + e z₂²`; hence `Q W + c W` is unbounded above there, for every `c > 0`. -/
theorem wLyapFamily_no_exponential_drift (κ : closedLoop.RateConstants) (α β δ e : ℝ)
    (hδ : 0 < δ) (he : 0 ≤ e) (c : ℝ) (hc : 0 < c) (K : ℝ) :
    ∃ n : Fin 3 → ℕ, closedLoop.observableGenerator κ (wLyapFamily κ α β δ e) n >
      -c * wLyapFamily κ α β δ e n + K := by
  set B0 : ℝ := μ κ * (β - δ + e) - γ κ * α + θ κ * δ + θ κ * e with hB0
  have hcδ : 0 < c * δ := mul_pos hc hδ
  set M : ℝ := max 2 (max (2 * |θ κ - μ κ| / c) ((K - B0 - c * α) / (c * δ))) with hMdef
  obtain ⟨m, hm⟩ := exists_nat_gt M
  have hmM : M < (m : ℝ) := by exact_mod_cast hm
  have hm2 : 2 ≤ m := by
    have h : 2 < (m : ℝ) := by
      have h2 : (2 : ℝ) ≤ M := by
        rw [hMdef]; exact le_max_left _ _
      linarith
    exact_mod_cast (le_of_lt h)
  have hmA : (2 * |θ κ - μ κ| / c) < (m : ℝ) := by
    have h2 : (2 * |θ κ - μ κ| / c) ≤ M := by
      rw [hMdef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
    linarith
  have hmB : ((K - B0 - c * α) / (c * δ)) < (m : ℝ) := by
    have h2 : ((K - B0 - c * α) / (c * δ)) ≤ M := by
      rw [hMdef]; exact le_trans (le_max_right _ _) (le_max_right _ _)
    linarith
  have hcm : 2 * |θ κ - μ κ| ≤ c * (m : ℝ) := by
    rw [div_lt_iff₀ hc] at hmA
    nlinarith
  have hcdm : K - B0 - c * α < c * δ * (m : ℝ) := by
    rw [div_lt_iff₀ hcδ] at hmB
    nlinarith
  -- the value of the family on the line `z₁ = 0`
  have hW : wLyapFamily κ α β δ e (mk3 0 m 1) = α + δ * (m : ℝ) + e * (m : ℝ) ^ 2 := by
    rw [wLyapFamily_of_lt κ (by rw [mk3_zero, mk3_one]; omega)]
    simp only [mk3_zero, mk3_one, mk3_two]
    push_cast; ring
  -- its drift there
  have hd := drift_wLyapFamily_at κ α β δ e m hm2
  have hd' : closedLoop.observableGenerator κ (wLyapFamily κ α β δ e) (mk3 0 m 1)
      = 2 * e * (θ κ - μ κ) * (m : ℝ) + B0 := by
    rw [Network.observableGenerator_eq_jumpSystem_drift, hd]
    simp only [hB0]
    ring
  -- the quadratic part in `m` dominates the linear part
  have hkey : 0 ≤ e * (c * (m : ℝ) ^ 2 + 2 * (θ κ - μ κ) * (m : ℝ)) := by
    have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
    have habs' : -|θ κ - μ κ| ≤ θ κ - μ κ := neg_abs_le _
    have hinner : 0 ≤ c * (m : ℝ) + 2 * (θ κ - μ κ) := by linarith
    have hmul : 0 ≤ (m : ℝ) * (c * (m : ℝ) + 2 * (θ κ - μ κ)) := mul_nonneg hm0 hinner
    have heq : (m : ℝ) * (c * (m : ℝ) + 2 * (θ κ - μ κ)) =
        c * (m : ℝ) ^ 2 + 2 * (θ κ - μ κ) * (m : ℝ) := by ring
    have hmul' : 0 ≤ c * (m : ℝ) ^ 2 + 2 * (θ κ - μ κ) * (m : ℝ) := by
      rw [← heq]; exact hmul
    exact mul_nonneg he hmul'
  refine ⟨mk3 0 m 1, ?_⟩
  rw [hd', hW]
  nlinarith [hkey]

/-- **The candidate carries no exponential drift.**  This is the negation of the exponential-drift
hypothesis of `CRNT.Antithetic.closedLoop_geometric_ergodic_of_exponential_drift` for the
candidate `wLyap2`. -/
theorem wLyap2_no_exponential_drift (κ : closedLoop.RateConstants) (c : ℝ) (hc : 0 < c) (K : ℝ) :
    ∃ n : Fin 3 → ℕ, closedLoop.observableGenerator κ (wLyap2 κ) n > -c * wLyap2 κ n + K := by
  have hδ : 0 < cd κ := cd_pos κ
  obtain ⟨n, hn⟩ :=
    wLyapFamily_no_exponential_drift κ (cb κ) (cd κ) (cd κ) 0 hδ (by norm_num) c hc K
  have hfun : (wLyap2 κ) = (wLyapFamily κ (cb κ) (cd κ) (cd κ) 0) := by
    funext n; rfl
  refine ⟨n, ?_⟩
  rw [hfun]
  exact hn

/-- **The candidate carries no exponential drift certificate.**  Consequently the geometric
ergodicity of the antithetic closed loop is *not* obtained from the candidate: the hypothesis of
`CRNT.Antithetic.closedLoop_geometric_ergodic_of_exponential_drift` with `W = wLyap2` is
unsatisfiable. -/
theorem wLyap2_no_exponentialDriftCertificate (κ : closedLoop.RateConstants) :
    ¬ ∃ c K : ℝ, Stochastic.ExponentialDriftCertificate closedLoop κ (wLyap2 κ) c K := by
  rintro ⟨c, K, hC⟩
  have hc := hC.hc
  have hK := hC.hK
  obtain ⟨n, hn⟩ := wLyap2_no_exponential_drift κ c hc K
  have h1 : closedLoop.observableGenerator κ (wLyap2 κ) n ≤ -c * wLyap2 κ n + K := by
    exact hC.hdrift n
  linarith

/-! ## The sharp obstruction: any slope profile fails -/

/-- **A family which is *affine in `z₂`* on the region `z₁ < z₂`, with a slope `s (z₁)` that depends
on `z₁` but not on `x`.**  This is the most general shape of the candidates of the campaign (a
quadratic in `x` and `z₁`, plus a term affine in `z₂`). -/
noncomputable def wLyapSlope (κ : closedLoop.RateConstants) (α β : ℝ) (s : ℕ → ℝ)
    (n : Fin 3 → ℕ) : ℝ :=
  if n 1 ≤ n 0 then lyap κ n
  else α * (n 2 : ℝ) ^ 2 + β * (n 0 : ℝ) ^ 2 + s (n 0) * ((n 1 : ℝ) - (n 0 : ℝ))

/-- On the region `z₂ ≤ z₁` the family is the piecewise quadratic `lyap`. -/
theorem wLyapSlope_of_le {n : Fin 3 → ℕ} (h : n 1 ≤ n 0) :
    wLyapSlope κ α β s n = lyap κ n := by
  unfold wLyapSlope
  rw [if_pos h]

/-- On the region `z₁ < z₂` the family is `α x² + β z₁² + s (z₁) (z₂ − z₁)`. -/
theorem wLyapSlope_of_lt {n : Fin 3 → ℕ} (h : n 0 < n 1) :
    wLyapSlope κ α β s n = α * (n 2 : ℝ) ^ 2 + β * (n 0 : ℝ) ^ 2 +
      s (n 0) * ((n 1 : ℝ) - (n 0 : ℝ)) := by
  unfold wLyapSlope
  rw [if_neg (by omega)]

/-- **The exact drift of the slope family on the line `z₁ = 0`.** -/
theorem drift_wLyapSlope_zero (κ : closedLoop.RateConstants) (α β : ℝ) (s : ℕ → ℝ) (m : ℕ)
    (hm : 2 ≤ m) :
    (closedLoop.jumpSystem κ).drift (wLyapSlope κ α β s) (mk3 0 m 1) =
      μ κ * (s 1 - s 0) * (m : ℝ) + (μ κ * (β - s 1) - γ κ * α + θ κ * s 0) := by
  obtain ⟨r0, r1, r2, r3, r4⟩ := rate_eq κ (mk3 0 m 1)
  show ∑ r : closedLoop.R, closedLoop.stochasticMassActionRate κ (mk3 0 m 1) r *
      (wLyapSlope κ α β s (closedLoop.jumpNextCount (mk3 0 m 1) r) -
        wLyapSlope κ α β s (mk3 0 m 1)) = _
  change ∑ r : Fin 5, _ = _
  rw [Fin.sum_univ_five]
  have hnext0 : closedLoop.jumpNextCount (mk3 0 m 1) (0 : Fin 5) = mk3 1 m 1 := by
    funext i; fin_cases i <;> simp [jumpNextCount, closedLoop, rxn, mk3]
  have hnext3 : closedLoop.jumpNextCount (mk3 0 m 1) (3 : Fin 5) = mk3 0 m 0 := by
    funext i; fin_cases i <;> simp [jumpNextCount, closedLoop, rxn, mk3]
  have hnext4 : closedLoop.jumpNextCount (mk3 0 m 1) (4 : Fin 5) = mk3 0 (m + 1) 1 := by
    funext i; fin_cases i <;> simp [jumpNextCount, closedLoop, rxn, mk3]
  have hA : (mk3 1 m 1 : Fin 3 → ℕ) 0 < (mk3 1 m 1 : Fin 3 → ℕ) 1 := by
    rw [mk3_zero, mk3_one]; omega
  have hB : (mk3 0 m 1 : Fin 3 → ℕ) 0 < (mk3 0 m 1 : Fin 3 → ℕ) 1 := by
    rw [mk3_zero, mk3_one]; omega
  have hD : (mk3 0 m 0 : Fin 3 → ℕ) 0 < (mk3 0 m 0 : Fin 3 → ℕ) 1 := by
    rw [mk3_zero, mk3_one]; omega
  have hE : (mk3 0 (m + 1) 1 : Fin 3 → ℕ) 0 < (mk3 0 (m + 1) 1 : Fin 3 → ℕ) 1 := by
    rw [mk3_zero, mk3_one]; omega
  have t0 : closedLoop.stochasticMassActionRate κ (mk3 0 m 1) (0 : Fin 5) *
        (wLyapSlope κ α β s (closedLoop.jumpNextCount (mk3 0 m 1) (0 : Fin 5)) -
          wLyapSlope κ α β s (mk3 0 m 1)) =
      μ κ * (β + s 1 * ((m : ℝ) - 1) - s 0 * (m : ℝ)) := by
    rw [r0, hnext0, wLyapSlope_of_lt κ hA, wLyapSlope_of_lt κ hB]
    simp only [mk3_zero, mk3_one, mk3_two]
    push_cast; ring
  have t1 : closedLoop.stochasticMassActionRate κ (mk3 0 m 1) (1 : Fin 5) *
        (wLyapSlope κ α β s (closedLoop.jumpNextCount (mk3 0 m 1) (1 : Fin 5)) -
          wLyapSlope κ α β s (mk3 0 m 1)) = 0 := by
    rw [r1]
    simp only [mk3_zero]
    push_cast
    ring
  have t2 : closedLoop.stochasticMassActionRate κ (mk3 0 m 1) (2 : Fin 5) *
        (wLyapSlope κ α β s (closedLoop.jumpNextCount (mk3 0 m 1) (2 : Fin 5)) -
          wLyapSlope κ α β s (mk3 0 m 1)) = 0 := by
    rw [r2]
    simp only [mk3_zero]
    push_cast
    ring
  have t3 : closedLoop.stochasticMassActionRate κ (mk3 0 m 1) (3 : Fin 5) *
        (wLyapSlope κ α β s (closedLoop.jumpNextCount (mk3 0 m 1) (3 : Fin 5)) -
          wLyapSlope κ α β s (mk3 0 m 1)) = γ κ * (-α) := by
    rw [r3, hnext3, wLyapSlope_of_lt κ hD, wLyapSlope_of_lt κ hB]
    simp only [mk3_zero, mk3_one, mk3_two]
    push_cast; ring
  have t4 : closedLoop.stochasticMassActionRate κ (mk3 0 m 1) (4 : Fin 5) *
        (wLyapSlope κ α β s (closedLoop.jumpNextCount (mk3 0 m 1) (4 : Fin 5)) -
          wLyapSlope κ α β s (mk3 0 m 1)) = θ κ * s 0 := by
    rw [r4, hnext4, wLyapSlope_of_lt κ hE, wLyapSlope_of_lt κ hB]
    simp only [mk3_zero, mk3_one, mk3_two]
    push_cast; ring
  rw [t0, t1, t2, t3, t4]
  ring

/-- **The exact drift of the slope family on the line `z₁ = 1`.**  The annihilation is now active
(rate `η z₂`) and contributes a term of order `z₂²`. -/
theorem drift_wLyapSlope_one (κ : closedLoop.RateConstants) (α β : ℝ) (s : ℕ → ℝ) (m : ℕ)
    (hm : 3 ≤ m) :
    (closedLoop.jumpSystem κ).drift (wLyapSlope κ α β s) (mk3 1 m 1) =
      η κ * (s 0 - s 1) * (m : ℝ) ^ 2 +
        (μ κ * (s 2 - s 1) + η κ * (s 1 - s 0 - β)) * (m : ℝ) +
        (μ κ * (3 * β - 2 * s 2 + s 1) + 3 * kk κ * α + θ κ * s 1 - γ κ * α) := by
  obtain ⟨r0, r1, r2, r3, r4⟩ := rate_eq κ (mk3 1 m 1)
  show ∑ r : closedLoop.R, closedLoop.stochasticMassActionRate κ (mk3 1 m 1) r *
      (wLyapSlope κ α β s (closedLoop.jumpNextCount (mk3 1 m 1) r) -
        wLyapSlope κ α β s (mk3 1 m 1)) = _
  change ∑ r : Fin 5, _ = _
  rw [Fin.sum_univ_five]
  have hnext0 : closedLoop.jumpNextCount (mk3 1 m 1) (0 : Fin 5) = mk3 2 m 1 := by
    funext i; fin_cases i <;> simp [jumpNextCount, closedLoop, rxn, mk3]
  have hnext1 : closedLoop.jumpNextCount (mk3 1 m 1) (1 : Fin 5) = mk3 0 (m - 1) 1 := by
    funext i; fin_cases i <;> simp [jumpNextCount, closedLoop, rxn, mk3]
  have hnext2 : closedLoop.jumpNextCount (mk3 1 m 1) (2 : Fin 5) = mk3 1 m 2 := by
    funext i; fin_cases i <;> simp [jumpNextCount, closedLoop, rxn, mk3]
  have hnext3 : closedLoop.jumpNextCount (mk3 1 m 1) (3 : Fin 5) = mk3 1 m 0 := by
    funext i; fin_cases i <;> simp [jumpNextCount, closedLoop, rxn, mk3]
  have hnext4 : closedLoop.jumpNextCount (mk3 1 m 1) (4 : Fin 5) = mk3 1 (m + 1) 1 := by
    funext i; fin_cases i <;> simp [jumpNextCount, closedLoop, rxn, mk3]
  have hA : (mk3 2 m 1 : Fin 3 → ℕ) 0 < (mk3 2 m 1 : Fin 3 → ℕ) 1 := by
    rw [mk3_zero, mk3_one]; omega
  have hB : (mk3 1 m 1 : Fin 3 → ℕ) 0 < (mk3 1 m 1 : Fin 3 → ℕ) 1 := by
    rw [mk3_zero, mk3_one]; omega
  have hC : (mk3 0 (m - 1) 1 : Fin 3 → ℕ) 0 < (mk3 0 (m - 1) 1 : Fin 3 → ℕ) 1 := by
    rw [mk3_zero, mk3_one]; omega
  have hD : (mk3 1 m 0 : Fin 3 → ℕ) 0 < (mk3 1 m 0 : Fin 3 → ℕ) 1 := by
    rw [mk3_zero, mk3_one]; omega
  have hE : (mk3 1 (m + 1) 1 : Fin 3 → ℕ) 0 < (mk3 1 (m + 1) 1 : Fin 3 → ℕ) 1 := by
    rw [mk3_zero, mk3_one]; omega
  have hF : (mk3 1 m 2 : Fin 3 → ℕ) 0 < (mk3 1 m 2 : Fin 3 → ℕ) 1 := by
    rw [mk3_zero, mk3_one]; omega
  have t0 : closedLoop.stochasticMassActionRate κ (mk3 1 m 1) (0 : Fin 5) *
        (wLyapSlope κ α β s (closedLoop.jumpNextCount (mk3 1 m 1) (0 : Fin 5)) -
          wLyapSlope κ α β s (mk3 1 m 1)) =
      μ κ * (3 * β + s 2 * ((m : ℝ) - 2) - s 1 * ((m : ℝ) - 1)) := by
    rw [r0, hnext0, wLyapSlope_of_lt κ hA, wLyapSlope_of_lt κ hB]
    simp only [mk3_zero, mk3_one, mk3_two]
    push_cast; ring
  have t1 : closedLoop.stochasticMassActionRate κ (mk3 1 m 1) (1 : Fin 5) *
        (wLyapSlope κ α β s (closedLoop.jumpNextCount (mk3 1 m 1) (1 : Fin 5)) -
          wLyapSlope κ α β s (mk3 1 m 1)) =
      η κ * (m : ℝ) * (s 0 * ((m : ℝ) - 1) - β - s 1 * ((m : ℝ) - 1)) := by
    rw [r1, hnext1, wLyapSlope_of_lt κ hC, wLyapSlope_of_lt κ hB]
    simp only [mk3_zero, mk3_one, mk3_two]
    have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : (1 : ℕ) ≤ m)]
      norm_num
    rw [hcast]
    ring
  have t2 : closedLoop.stochasticMassActionRate κ (mk3 1 m 1) (2 : Fin 5) *
        (wLyapSlope κ α β s (closedLoop.jumpNextCount (mk3 1 m 1) (2 : Fin 5)) -
          wLyapSlope κ α β s (mk3 1 m 1)) = kk κ * (3 * α) := by
    rw [r2, hnext2, wLyapSlope_of_lt κ hF, wLyapSlope_of_lt κ hB]
    simp only [mk3_zero, mk3_one, mk3_two]
    push_cast; ring
  have t3 : closedLoop.stochasticMassActionRate κ (mk3 1 m 1) (3 : Fin 5) *
        (wLyapSlope κ α β s (closedLoop.jumpNextCount (mk3 1 m 1) (3 : Fin 5)) -
          wLyapSlope κ α β s (mk3 1 m 1)) = γ κ * (-α) := by
    rw [r3, hnext3, wLyapSlope_of_lt κ hD, wLyapSlope_of_lt κ hB]
    simp only [mk3_zero, mk3_one, mk3_two]
    push_cast; ring
  have t4 : closedLoop.stochasticMassActionRate κ (mk3 1 m 1) (4 : Fin 5) *
        (wLyapSlope κ α β s (closedLoop.jumpNextCount (mk3 1 m 1) (4 : Fin 5)) -
          wLyapSlope κ α β s (mk3 1 m 1)) = θ κ * s 1 := by
    rw [r4, hnext4, wLyapSlope_of_lt κ hE, wLyapSlope_of_lt κ hB]
    simp only [mk3_zero, mk3_one, mk3_two]
    push_cast; ring
  rw [t0, t1, t2, t3, t4]
  ring

/-- **A linear function which is bounded above on a half line has a nonpositive slope.**  The
argument is Archimedean: if the slope were positive, the function would exceed the bound for a
large enough argument. -/
theorem lin_bounded_above {A B K : ℝ} (h : ∀ m : ℕ, 2 ≤ m → A * (m : ℝ) + B ≤ K) : A ≤ 0 := by
  by_contra hA
  push Not at hA
  have hA' : 0 < A := by linarith
  obtain ⟨t, ht⟩ := exists_nat_gt ((K - A * 2 - B) / A)
  have ht' : (K - A * 2 - B) / A < (t : ℝ) := by exact_mod_cast ht
  have h1 : K - A * 2 - B < A * (t : ℝ) := by
    rw [div_lt_iff₀ hA'] at ht'
    linarith
  have h2 := h (2 + t) (by omega)
  rw [Nat.cast_add, Nat.cast_two] at h2
  linarith

/-- **A quadratic polynomial which is bounded above on a half line has a nonpositive leading
coefficient.** -/
theorem quad_bounded_above {A B C K : ℝ}
    (h : ∀ m : ℕ, 3 ≤ m → A * (m : ℝ) ^ 2 + B * (m : ℝ) + C ≤ K) : A ≤ 0 := by
  by_contra hA
  push Not at hA
  have hA' : 0 < A := by linarith
  obtain ⟨m, hm⟩ := exists_nat_gt (max 3 ((|B| + |K| + |C| + 1) / A))
  have hm' : (|B| + |K| + |C| + 1) / A < (m : ℝ) := by
    have h2 : (|B| + |K| + |C| + 1) / A ≤ max 3 ((|B| + |K| + |C| + 1) / A) :=
      le_max_right _ _
    linarith
  have hAm : |B| + |K| + |C| + 1 < A * (m : ℝ) := by
    rw [div_lt_iff₀ hA'] at hm'
    linarith
  have hm3 : 3 ≤ m := by
    have h1 : 3 < (m : ℝ) := by
      have h2 : (3 : ℝ) ≤ max 3 ((|B| + |K| + |C| + 1) / A) := le_max_left _ _
      linarith
    exact_mod_cast (le_of_lt h1)
  have hcond := h m hm3
  have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
  have hm1 : 1 ≤ (m : ℝ) := by
    have : (1 : ℕ) ≤ m := by omega
    exact_mod_cast this
  have hmul : (m : ℝ) * (|B| + |K| + |C| + 1) ≤ (m : ℝ) * (A * (m : ℝ)) :=
    mul_le_mul_of_nonneg_left (le_of_lt hAm) hm0
  have hmul' : (|B| + |K| + |C| + 1) * (m : ℝ) ≤ A * (m : ℝ) ^ 2 := by
    rw [show (m : ℝ) * (A * (m : ℝ)) = A * (m : ℝ) ^ 2 by ring] at hmul
    nlinarith [hmul]
  have habsB : -|B| * (m : ℝ) ≤ B * (m : ℝ) := mul_le_mul_of_nonneg_right (neg_abs_le B) hm0
  have habsC : -|C| ≤ C := neg_abs_le C
  have hKm : |K| ≤ |K| * (m : ℝ) := by
    simpa using (mul_le_mul_of_nonneg_left hm1 (abs_nonneg K))
  have hCm : |C| ≤ |C| * (m : ℝ) := by
    simpa using (mul_le_mul_of_nonneg_left hm1 (abs_nonneg C))
  have h1 : K < A * (m : ℝ) ^ 2 + B * (m : ℝ) + C := by
    nlinarith [hmul', habsB, habsC, hKm, hCm, hm1, le_abs_self K]
  linarith

/-- **The sharp obstruction.**  *No* function which is affine in `z₂` on the region `z₁ < z₂`, with
a slope that depends on `z₁` but not on `x`, carries an exponential drift — provided the slope on
the line `z₁ = 0` is positive, which is *necessary* for the finite sublevel sets.

The proof is the two-line argument of the docstring.  On the line `z₁ = 0` the sensing direction
contributes `+ θ s 0 > 0` and the drift condition forces the coefficient of `z₂` in `Q W + c W` to
be nonpositive, i.e. `μ (s 1 − s 0) + c s 0 ≤ 0`: the slope must *drop* from `z₁ = 0` to `z₁ = 1`.
On the line `z₁ = 1` the annihilation is active and contributes `η z₂ (W(0, z₂ − 1) − W(1, z₂))`,
whose coefficient of `z₂²` is `η (s 0 − s 1)`; the drift condition forces it to be nonpositive,
i.e. `s 0 ≤ s 1`: the slope must *not* drop.  The two requirements contradict each other. -/
theorem wLyapSlope_no_exponential_drift (κ : closedLoop.RateConstants) (α β : ℝ) (s : ℕ → ℝ)
    (hs0 : 0 < s 0) (c : ℝ) (hc : 0 < c) (K : ℝ) :
    ∃ n : Fin 3 → ℕ, closedLoop.observableGenerator κ (wLyapSlope κ α β s) n >
      -c * wLyapSlope κ α β s n + K := by
  by_contra hcon
  push Not at hcon
  have hμ : 0 < μ κ := (params_pos κ).1
  -- the drift condition on the line `z₁ = 0`
  have hzero : ∀ m : ℕ, 2 ≤ m →
      (μ κ * (s 1 - s 0) + c * s 0) * (m : ℝ) +
          (μ κ * (β - s 1) - γ κ * α + θ κ * s 0 + c * α) ≤ K := by
    intro m hm
    have h1 := hcon (mk3 0 m 1)
    rw [Network.observableGenerator_eq_jumpSystem_drift] at h1
    have hd := drift_wLyapSlope_zero κ α β s m hm
    have hW : wLyapSlope κ α β s (mk3 0 m 1) = α + s 0 * (m : ℝ) := by
      rw [wLyapSlope_of_lt κ (by rw [mk3_zero, mk3_one]; omega)]
      simp only [mk3_zero, mk3_one, mk3_two]
      push_cast; ring
    rw [hd, hW] at h1
    linarith
  have hA : μ κ * (s 1 - s 0) + c * s 0 ≤ 0 :=
    lin_bounded_above hzero
  -- the drift condition on the line `z₁ = 1`
  have hone : ∀ m : ℕ, 3 ≤ m →
      η κ * (s 0 - s 1) * (m : ℝ) ^ 2 +
        (μ κ * (s 2 - s 1) + η κ * (s 1 - s 0 - β) + c * s 1) * (m : ℝ) +
        (μ κ * (3 * β - 2 * s 2 + s 1) + 3 * kk κ * α + θ κ * s 1 - γ κ * α +
          c * (α + β - s 1)) ≤ K := by
    intro m hm
    have h1 := hcon (mk3 1 m 1)
    rw [Network.observableGenerator_eq_jumpSystem_drift] at h1
    have hd := drift_wLyapSlope_one κ α β s m hm
    have hW : wLyapSlope κ α β s (mk3 1 m 1) = α + β + s 1 * ((m : ℝ) - 1) := by
      rw [wLyapSlope_of_lt κ (by rw [mk3_zero, mk3_one]; omega)]
      simp only [mk3_zero, mk3_one, mk3_two]
      push_cast; ring
    rw [hd, hW] at h1
    linarith
  have hB : η κ * (s 0 - s 1) ≤ 0 := quad_bounded_above hone
  -- the contradiction
  have hη : 0 < η κ := (params_pos κ).2.1
  have h1 : s 0 ≤ s 1 := by
    by_contra hlt
    have hlt' : s 1 < s 0 := by linarith
    have : η κ * (s 0 - s 1) > 0 := by positivity
    linarith
  have h2 : 0 ≤ μ κ * (s 1 - s 0) := by
    have : 0 ≤ s 1 - s 0 := by linarith
    positivity
  nlinarith

/-- **The negation of the exponential-drift statement for the candidate.**  There are no
`c > 0` and `K` for which `Q wLyap2 ≤ −c wLyap2 + K` holds at every count. -/
theorem wLyap2_no_exponentialDrift_exists (κ : closedLoop.RateConstants) :
    ¬ ∃ c K : ℝ, 0 < c ∧ 0 ≤ K ∧
        ∀ n, closedLoop.observableGenerator κ (wLyap2 κ) n ≤ -c * wLyap2 κ n + K := by
  rintro ⟨c, K, hc, hK, h⟩
  obtain ⟨n, hn⟩ := wLyap2_no_exponential_drift κ c hc K
  have h1 := h n
  linarith

end Antithetic
end CRNT

#print axioms CRNT.Antithetic.wLyap2_nonneg
#print axioms CRNT.Antithetic.wLyap2_le_lyap
#print axioms CRNT.Antithetic.drift_wLyap2_le_regionA
#print axioms CRNT.Antithetic.wLyap2_finite
#print axioms CRNT.Antithetic.drift_wLyapFamily_at
#print axioms CRNT.Antithetic.wLyapFamily_no_exponential_drift
#print axioms CRNT.Antithetic.wLyap2_no_exponential_drift
#print axioms CRNT.Antithetic.wLyap2_no_exponentialDriftCertificate
#print axioms CRNT.Antithetic.wLyap2_no_exponentialDrift_exists
#print axioms CRNT.Antithetic.drift_wLyapSlope_zero
#print axioms CRNT.Antithetic.drift_wLyapSlope_one
#print axioms CRNT.Antithetic.lin_bounded_above
#print axioms CRNT.Antithetic.quad_bounded_above
#print axioms CRNT.Antithetic.wLyapSlope_no_exponential_drift
