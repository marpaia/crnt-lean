import CRNT.Theorems.DeficiencyZero.Dissipation
import CRNT.Theorems.DeficiencyZero.Lyapunov
import CRNT.Theorems.DeficiencyZero.Stability
import CRNT.Equilibria.DetailedBalanceEntropy
import CRNT.Examples.ReversiblePair

/-!
# The sum-of-squares form of the entropy dissipation

## The classical identity

Horn and Jackson (*General mass action kinetics*, Arch. Rational Mech. Anal. **47** (1972),
81–116) show that the relative entropy (their *pseudo-Helmholtz free energy*)

```text
G(x) = ∑ᵢ (xᵢ log(xᵢ/x*ᵢ) − xᵢ + x*ᵢ)
```

is a Lyapunov function for the mass-action dynamics: along a solution, `d/dt G ≤ 0`, with
equality exactly at the complex-balanced states.  This repository already contains that
statement:

* `CRNT.Network.dissipation_nonpos` — the **Gibbs bound**
  `⟨log(x/x*), f(x)⟩ ≤ 0` for a positive complex-balanced reference `x*`;
* `CRNT.Network.complexBalanced_of_dissipation_eq_zero` and
  `CRNT.Network.dissipation_eq_zero_of_complexBalanced` — the strictness;
* `CRNT.relEntropy` (`CRNT/Theorems/DeficiencyZero/Lyapunov.lean`) — the Lyapunov function
  itself, nonnegative and vanishing only at the reference;
* `CRNT.Network.complexBalanced_hasStrictStoichQuadraticLyapunov` and
  `CRNT.Network.complexBalanced_isHurwitzOnStoich` (leaf D21,
  `CRNT/Equilibria/ComplexBalanceLinearStability.lean`) — the **linearization theorem**
  with the strict quadratic Lyapunov function (the entropy Hessian `diag(1/x*ᵢ)`);
* `CRNT.Network.relEntropy_expDecay_along_solution` (leaf D4,
  `CRNT/Theorems/DeficiencyZero/DecayRate.lean`) — the **exponential decay with a prefactor**.

What is missing is the *quantitative* form of the dissipation: the **sum of squares**.  The
identity one wants is

```text
d/dt G(x(t)) = −(1/2) ∑_r q_r(x) ⟨ν_r, D(x*)⁻¹ h⟩² ,      h = log(x/x*) ,
```

with `q_r(x)` the forward flux of reaction `r` and `ν_r` its reaction vector.  It is this
identity, and not the Gibbs bound, that makes the relative entropy a *strict* Lyapunov
function with a **rate**: the entropy production is literally a sum of squares, so it
vanishes only when every reaction is "at equilibrium" in the logarithmic sense, and it is
bounded below by a definite multiple of the entropy itself near the equilibrium.  This is
the "thermodynamic speed limit" reading of the entropy production.

## What this module proves — and what it does not

**The naive identity is false.**  The identity above is *not* an identity.  For the reversible
pair `A ⇌ B` with unit rate constants, the complex-balanced reference `x* = (2, 2)` and the
state `x = (4, 2)` one computes

```text
∑_r q_r(x) ⟨ν_r, D(x*)⁻¹ h⟩²  =  (3/2) (log 2)²   ≈ 0.7207 ,
−2 ⟨log(x/x*), f(x)⟩          =  4 log 2           ≈ 2.7726 ,
```

so the two sides differ; equality would force `log 2 = 8/3`, whereas `log 2 < 1`.  This
counterexample is machine-checked: `CRNT.Network.reversiblePair_naiveIdentity_fails`.  (With
the reference `x* = (1, 1)` and the state `x = (2, 1)` the discrepancy is smaller but still
present: `3 (log 2)² ≈ 1.4414` versus `2 log 2 ≈ 1.3863`.)

The reason is structural: the sum of squares above is the *quadratic* part of the
dissipation (it is the nonlinear version of the second-variation identity
`CRNT.Network.complexBalanceJacobianQuadratic_eq_neg_sum_sq`), while the entropy
dissipation has a cubic remainder.  Consequently the global inequality
`⟨log(x/x*), f(x)⟩ ≤ −(1/2) ∑_r q_r(x) ⟨ν_r, D(x*)⁻¹ h⟩²` is false as well: for the
reversible pair with `x* = (1, 1)` at `x = (1/2, 1)` the left-hand side is
`−(log 2)/2 ≈ −0.3466` whereas the right-hand side is `−(3/4)(log 2)² ≈ −0.3603`.

What *is* true, and is proved here, is the following **exact decomposition**
(`CRNT.Network.entropyDissipation_eq_sum_squares`):

```text
⟨log(x/x*), f(x)⟩  =  −(1/2) ∑_r q_r(x*) ⟨ν_r, log(x/x*)⟩²
                      + ∑_r q_r(x*) (x^{y_r}/x*^{y_r} − 1 − log(x^{y_r}/x*^{y_r})) ⟨ν_r, log(x/x*)⟩ ,
```

i.e. the dissipation is the **negative of a weighted sum of squares** — the squares of the
logarithmic ratios across the reactions, weighted by the equilibrium reaction fluxes —
plus an explicit remainder, the cubic deviation of the exponential expansion of the source
monomials.  The remainder is nonnegative *term by term* (`exp u ≥ 1 + u`), and it is
`O(‖h‖³)` near the equilibrium, so the sum of squares is the exact quadratic part of the
dissipation.

The ingredients are:

* `CRNT.Network.complexLogRatio`, `CRNT.Network.reactionLogRatio` — the logarithmic ratios
  `log(x^c/x*^c)` and their differences across a reaction;
* `CRNT.Network.entropyDissipation_eq_fluxLogRatio` — the exact *flux* form of the
  dissipation, `⟨log(x/x*), f(x)⟩ = ∑_r q_r(x) ⟨ν_r, log(x/x*)⟩`, which is the algebraic
  core of the identity and holds without any complex-balance hypothesis;
* `CRNT.Network.complexBalance_fluxBalance` — the complex-balance balance of the
  equilibrium fluxes against *any* function of the complex logarithmic ratios; this is the
  step that produces the squares;
* `CRNT.Network.entropyDissipation_eq_sum_squares` — the sum-of-squares decomposition;
* `CRNT.Network.relEntropy_hasDerivAt_sum_squares` — the same identity along a trajectory,
  i.e. the sum-of-squares form of `d/dt G`;
* `CRNT.Network.naiveLogSumSquares` and
  `CRNT.Network.reversiblePair_naiveIdentity_fails` — the *naive* sum of squares of the
  Horn–Jackson formula, and the machine-checked counterexample showing that it is not the
  entropy dissipation.

## What is *not* claimed

* **Not the global statement.**  The global exponential decay of the relative entropy with a
  *constant-one prefactor* does **not** follow: the exact identity carries a remainder, and
  the naive global sum-of-squares identity is false (see above).  The quantitative content
  that is available is the *local* one of leaf D4/D21.
* **Not the Onsager form.**  For a *detailed-balanced* network the entropy production is
  the classical Onsager expression `½ ∑_r (q_r − q_r^rev)(log q_r − log q_r^rev)`; that is
  `CRNT.Network.relativeLogDissipation_eq_neg_entropyProduction`
  (`CRNT/Equilibria/DetailedBalanceEntropy.lean`), and it is *not* re-proved here.  This
  module is about the *complex-balanced* case and the sum-of-squares form.
* **Not the Fisher-information decay.**  The "Fisher information" reading of the
  dissipation (`d/dt G = −(1/2) ∑_r q_r ⟨ν_r, D(x*)⁻¹ h⟩² ≤ −c G`) is the premise of the
  prefactor-free decay discussed in `CRNT/Theorems/DeficiencyZero/DecayRate.lean`; it is
  false as a global identity, and this module replaces it by the exact decomposition above.

## The worked instance

For the reversible pair `A ⇌ B` with forward rate `k₀` and backward rate `k₁`, the
detailed-balanced reference is `x* = (k₁, k₀)` and the dissipation reduces to the classical
two-term formula (`CRNT.Network.reversiblePair_entropyDissipation_eq_twoTerm`)

```text
⟨log(x/x*), f(x)⟩  =  (k₀ x_A − k₁ x_B) (log(k₁ x_B) − log(k₀ x_A))  ≤  0 .
```

-/

namespace CRNT

namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ## The logarithmic ratios -/

/-- The logarithmic ratio `log x − log x*` of two concentrations. -/
noncomputable def logRatioVector (x xstar : Concentration S) : Concentration S :=
  fun s => Real.log (x s) - Real.log (xstar s)

/-- The logarithmic ratio of the complex monomials: `log(x^c) − log(x*^c)`.  This is the
complex-space analogue of `logRatioVector`; it is the linear functional `⟨c, log(x/x*)⟩`. -/
noncomputable def complexLogRatio (N : Network S) (x xstar : Concentration S) :
    N.ComplexIdx → ℝ :=
  fun c => Real.log (N.complexMonomialVector x c) - Real.log (N.complexMonomialVector xstar c)

/-- The logarithmic ratio across reaction `r`: `ℓ_{tgt r} − ℓ_{src r}`.  This is the pairing
`⟨ν_r, log(x/x*)⟩` of the reaction vector with the logarithmic ratio. -/
noncomputable def reactionLogRatio (N : Network S) (x xstar : Concentration S) (r : N.R) : ℝ :=
  N.complexLogRatio x xstar (N.targetIdx r) - N.complexLogRatio x xstar (N.sourceIdx r)

/-- The remainder of the exponential expansion of the source monomial:
`exp(ℓ_c) − 1 − ℓ_c`.  It is nonnegative, and it is the cubic deviation that separates the
sum of squares from the exact entropy dissipation. -/
noncomputable def complexLogRemainder (N : Network S) (x xstar : Concentration S)
    (c : N.ComplexIdx) : ℝ :=
  Real.exp (N.complexLogRatio x xstar c) - 1 - N.complexLogRatio x xstar c

/-- The logarithmic ratio of a complex monomial is the linear pairing of the complex with
`log x − log x*`. -/
theorem complexLogRatio_eq_pairing (N : Network S) {x xstar : Concentration S}
    (hx : x.Positive) (hxs : xstar.Positive) (c : N.ComplexIdx) :
    N.complexLogRatio x xstar c
      = ∑ s, (c.val s : ℝ) * (Real.log (x s) - Real.log (xstar s)) := by
  unfold complexLogRatio
  rw [log_complexMonomialVector N hx, log_complexMonomialVector N hxs,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- The logarithmic ratio across a reaction is the pairing of the reaction vector with
`log x − log x*`. -/
theorem reactionLogRatio_eq_pairing (N : Network S) {x xstar : Concentration S}
    (hx : x.Positive) (hxs : xstar.Positive) (r : N.R) :
    N.reactionLogRatio x xstar r
      = ∑ s, (Real.log (x s) - Real.log (xstar s)) * N.reactionVector r s := by
  have h1 : N.complexLogRatio x xstar (N.targetIdx r)
      = ∑ s, ((N.reaction r).target s : ℝ) * (Real.log (x s) - Real.log (xstar s)) := by
    rw [complexLogRatio_eq_pairing N hx hxs]
    simp only [targetIdx]
  have h2 : N.complexLogRatio x xstar (N.sourceIdx r)
      = ∑ s, ((N.reaction r).source s : ℝ) * (Real.log (x s) - Real.log (xstar s)) := by
    rw [complexLogRatio_eq_pairing N hx hxs]
    simp only [sourceIdx]
  unfold reactionLogRatio
  rw [h1, h2]
  simp only [reactionVector_apply]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  ring

/-! ## The exact flux form of the dissipation -/

/-- **The logarithmic dissipation is the reaction-wise sum of the forward flux times the
logarithmic ratio across the reaction.**

This is the algebraic core of the Horn–Jackson identity, and it holds for *any* reference
`x*` — no complex-balance hypothesis is needed. -/
theorem entropyDissipation_eq_fluxLogRatio (N : Network S) (κ : N.RateConstants)
    {x xstar : Concentration S} (hx : x.Positive) (hxs : xstar.Positive) :
    N.relativeLogDissipation κ x xstar
      = ∑ r : N.R, N.massActionRate κ r x * N.reactionLogRatio x xstar r := by
  unfold relativeLogDissipation
  calc
    (∑ s, (Real.log (x s) - Real.log (xstar s)) * N.massActionVectorField κ x s)
        = ∑ s, ∑ r : N.R, (Real.log (x s) - Real.log (xstar s)) *
              (N.massActionRate κ r x * N.reactionVector r s) := by
            apply Finset.sum_congr rfl; intro s _
            rw [massActionVectorField_apply, Finset.mul_sum]
    _ = ∑ r : N.R, ∑ s : S, (Real.log (x s) - Real.log (xstar s)) *
              (N.massActionRate κ r x * N.reactionVector r s) := by
            exact Finset.sum_comm
    _ = ∑ r : N.R, N.massActionRate κ r x *
              (∑ s : S, (Real.log (x s) - Real.log (xstar s)) * N.reactionVector r s) := by
            apply Finset.sum_congr rfl; intro r _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro s _
            ring
    _ = ∑ r : N.R, N.massActionRate κ r x * N.reactionLogRatio x xstar r := by
            apply Finset.sum_congr rfl; intro r _
            rw [reactionLogRatio_eq_pairing N hx hxs]

/-- **Complex balance balances the equilibrium fluxes against any function of the complex
logarithmic ratios.**  This is the step that turns the flux form of the dissipation into a
sum of squares. -/
theorem complexBalance_fluxBalance (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hcb : N.IsComplexBalanced κ xstar)
    (φ : N.ComplexIdx → ℝ) :
    (∑ r : N.R, N.massActionRate κ r xstar *
        (φ (N.targetIdx r) - φ (N.sourceIdx r))) = 0 := by
  have hk : N.kineticMap κ (N.complexMonomialVector xstar) = 0 :=
    (N.isComplexBalanced_iff_kineticMap κ xstar).mp hcb
  have hpair : (∑ c : N.ComplexIdx, N.kineticMap κ (N.complexMonomialVector xstar) c * φ c)
      = ∑ r : N.R, N.massActionRate κ r xstar *
          (φ (N.targetIdx r) - φ (N.sourceIdx r)) := by
    rw [N.kineticMap_pairing]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [N.massActionRate_eq]
  rw [← hpair, hk]
  simp

/-- **The logarithmic dissipation is the reaction-wise sum of the *difference* of the forward
flux and the equilibrium flux times the logarithmic ratio across the reaction.**  Complex
balance is exactly what allows the equilibrium flux to be subtracted term by term. -/
theorem entropyDissipation_eq_eqFluxLogRatio (N : Network S) (κ : N.RateConstants)
    {x xstar : Concentration S} (hx : x.Positive) (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar) :
    N.relativeLogDissipation κ x xstar
      = ∑ r : N.R, (N.massActionRate κ r x - N.massActionRate κ r xstar) *
          N.reactionLogRatio x xstar r := by
  have h1 := entropyDissipation_eq_fluxLogRatio N κ hx hxs
  have h2 : (∑ r : N.R, N.massActionRate κ r xstar * N.reactionLogRatio x xstar r) = 0 := by
    have hss : N.IsMassActionSteadyState κ xstar := hcb.isMassActionSteadyState N κ
    calc
      (∑ r : N.R, N.massActionRate κ r xstar * N.reactionLogRatio x xstar r)
          = ∑ r : N.R, N.massActionRate κ r xstar *
              (∑ s : S, (Real.log (x s) - Real.log (xstar s)) * N.reactionVector r s) := by
            apply Finset.sum_congr rfl; intro r _
            rw [reactionLogRatio_eq_pairing N hx hxs]
      _ = ∑ s : S, ∑ r : N.R, N.massActionRate κ r xstar *
              ((Real.log (x s) - Real.log (xstar s)) * N.reactionVector r s) := by
            calc
              (∑ r : N.R, N.massActionRate κ r xstar *
                    (∑ s : S, (Real.log (x s) - Real.log (xstar s)) * N.reactionVector r s))
                  = ∑ r : N.R, ∑ s : S, N.massActionRate κ r xstar *
                      ((Real.log (x s) - Real.log (xstar s)) * N.reactionVector r s) := by
                    apply Finset.sum_congr rfl; intro r _
                    rw [Finset.mul_sum]
              _ = ∑ s : S, ∑ r : N.R, N.massActionRate κ r xstar *
                      ((Real.log (x s) - Real.log (xstar s)) * N.reactionVector r s) :=
                    Finset.sum_comm
      _ = ∑ s : S, (Real.log (x s) - Real.log (xstar s)) *
              N.massActionVectorField κ xstar s := by
            apply Finset.sum_congr rfl; intro s _
            rw [massActionVectorField_apply, Finset.mul_sum]
            apply Finset.sum_congr rfl; intro r _
            ring
      _ = 0 := by
            refine Finset.sum_eq_zero fun s _ => ?_
            rw [hss s, mul_zero]
  have hstep : (∑ r : N.R, (N.massActionRate κ r x - N.massActionRate κ r xstar) *
        N.reactionLogRatio x xstar r)
      = (∑ r : N.R, N.massActionRate κ r x * N.reactionLogRatio x xstar r)
        - ∑ r : N.R, N.massActionRate κ r xstar * N.reactionLogRatio x xstar r := by
    have hconv : ∀ r : N.R, (N.massActionRate κ r x - N.massActionRate κ r xstar) *
          N.reactionLogRatio x xstar r
        = N.massActionRate κ r x * N.reactionLogRatio x xstar r
          - N.massActionRate κ r xstar * N.reactionLogRatio x xstar r := by
      intro r; ring
    rw [Finset.sum_congr rfl (fun r _ => hconv r), Finset.sum_sub_distrib]
  unfold relativeLogDissipation at h1 ⊢
  rw [h1, hstep, h2, sub_zero]

/-! ## The sum-of-squares decomposition -/

/-- **The sum-of-squares form of the entropy dissipation.**

Relative to a positive complex-balanced reference `x*`, the logarithmic dissipation of the
relative entropy is the *negative* of a weighted sum of squares — the squares of the
logarithmic ratios across the reactions, weighted by the equilibrium reaction fluxes —
plus an explicit remainder, the cubic deviation of the exponential expansion of the source
monomials.

The sum-of-squares part is the exact **quadratic part** of the dissipation: it is the
nonlinear version of the second-variation identity
`CRNT.Network.complexBalanceJacobianQuadratic_eq_neg_sum_sq`. -/
theorem entropyDissipation_eq_sum_squares (N : Network S) (κ : N.RateConstants)
    {x xstar : Concentration S} (hx : x.Positive) (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar) :
    N.relativeLogDissipation κ x xstar
      = -(1 / 2 : ℝ) * ∑ r : N.R,
            N.massActionRate κ r xstar * (N.reactionLogRatio x xstar r)^2
        + ∑ r : N.R, N.massActionRate κ r xstar *
            N.complexLogRemainder x xstar (N.sourceIdx r) *
            N.reactionLogRatio x xstar r := by
  let u : N.R → ℝ := fun r => N.complexLogRatio x xstar (N.sourceIdx r)
  let v : N.R → ℝ := fun r => N.complexLogRatio x xstar (N.targetIdx r)
  let a : N.R → ℝ := fun r => v r - u r
  have ha : ∀ r : N.R, a r = N.reactionLogRatio x xstar r := by
    intro r
    show N.complexLogRatio x xstar (N.targetIdx r)
        - N.complexLogRatio x xstar (N.sourceIdx r) = N.reactionLogRatio x xstar r
    rfl
  have hrem : ∀ r : N.R, N.complexLogRemainder x xstar (N.sourceIdx r)
      = Real.exp (u r) - 1 - u r := by
    intro r; rfl
  -- the forward flux is the equilibrium flux times the exponential of the source ratio
  have hflux : ∀ r : N.R, N.massActionRate κ r x
      = N.massActionRate κ r xstar * Real.exp (u r) := by
    intro r
    have hmono := complexMonomialVector_eq_mul_exp N hx hxs (N.sourceIdx r)
    have hexp : (∑ s, ((N.sourceIdx r).val s : ℝ) *
        (Real.log (x s) - Real.log (xstar s))) = u r := by
      rw [← complexLogRatio_eq_pairing N hx hxs]
    rw [N.massActionRate_eq, N.massActionRate_eq, hmono, hexp]
    ring
  -- complex balance: the equilibrium fluxes balance the squares of the complex ratios
  have hbal : (∑ r : N.R, N.massActionRate κ r xstar * (v r ^ 2 - u r ^ 2)) = 0 := by
    have h := complexBalance_fluxBalance N κ hcb
      (fun c => (N.complexLogRatio x xstar c)^2)
    simpa only [u, v] using h
  -- the key algebraic identity: `2 ∑ Q_r u_r a_r + ∑ Q_r a_r² = 0`
  have hkey : 2 * (∑ r : N.R, N.massActionRate κ r xstar * (u r * a r))
      + ∑ r : N.R, N.massActionRate κ r xstar * (a r)^2 = 0 := by
    have hconv : ∀ r : N.R, 2 * (N.massActionRate κ r xstar * (u r * a r))
        + N.massActionRate κ r xstar * (a r)^2
        = N.massActionRate κ r xstar * (v r ^ 2 - u r ^ 2) := by
      intro r
      have ha' : a r = v r - u r := rfl
      ring
    rw [Finset.mul_sum, ← Finset.sum_add_distrib,
      Finset.sum_congr rfl (fun r _ => hconv r)]
    exact hbal
  have hkey' : (∑ r : N.R, N.massActionRate κ r xstar * (u r * a r))
      = -(1 / 2 : ℝ) * ∑ r : N.R, N.massActionRate κ r xstar * (a r)^2 := by
    linarith
  -- the dissipation is `∑_r Q_r (exp u_r − 1) a_r`
  have h1 : N.relativeLogDissipation κ x xstar
      = ∑ r : N.R, N.massActionRate κ r xstar * (Real.exp (u r) - 1) * (a r) := by
    have h := entropyDissipation_eq_eqFluxLogRatio N κ hx hxs hcb
    unfold relativeLogDissipation at h ⊢
    rw [h]
    have hconv : ∀ r : N.R,
        (N.massActionRate κ r x - N.massActionRate κ r xstar) *
            N.reactionLogRatio x xstar r
        = N.massActionRate κ r xstar * (Real.exp (u r) - 1) * (a r) := by
      intro r
      rw [ha r, hflux r]
      ring
    rw [Finset.sum_congr rfl (fun r _ => hconv r)]
  -- split `exp u − 1 = u + (exp u − 1 − u)`
  have h2 : (∑ r : N.R, N.massActionRate κ r xstar * (Real.exp (u r) - 1) * (a r))
      = (∑ r : N.R, N.massActionRate κ r xstar * (u r * a r))
        + ∑ r : N.R, N.massActionRate κ r xstar *
            (Real.exp (u r) - 1 - u r) * (a r) := by
    have hconv : ∀ r : N.R, N.massActionRate κ r xstar * (Real.exp (u r) - 1) * (a r)
        = N.massActionRate κ r xstar * (u r * a r)
          + N.massActionRate κ r xstar * (Real.exp (u r) - 1 - u r) * (a r) := by
      intro r; ring
    rw [Finset.sum_congr rfl (fun r _ => hconv r), Finset.sum_add_distrib]
  rw [h1, h2, hkey']
  have hconv : ∀ r : N.R, N.massActionRate κ r xstar * (Real.exp (u r) - 1 - u r) * (a r)
      = N.massActionRate κ r xstar * N.complexLogRemainder x xstar (N.sourceIdx r) *
          N.reactionLogRatio x xstar r := by
    intro r
    rw [hrem r, ha r]
  rw [Finset.sum_congr rfl (fun r _ => hconv r)]
  simp only [ha]

/-- **The sum of squares is nonnegative.**  The equilibrium fluxes are positive, so the
sum-of-squares part of the dissipation is a genuine sum of squares. -/
theorem entropyDissipation_sum_squares_nonneg (N : Network S) (κ : N.RateConstants)
    {x xstar : Concentration S} (hxs : xstar.Positive) :
    0 ≤ ∑ r : N.R, N.massActionRate κ r xstar * (N.reactionLogRatio x xstar r)^2 := by
  refine Finset.sum_nonneg fun r _ => ?_
  exact mul_nonneg (N.massActionRate_pos κ r hxs).le (sq_nonneg _)

/-- **The sum of squares vanishes exactly when every reaction is at logarithmic equilibrium.**
Since the equilibrium fluxes are strictly positive, the sum of squares vanishes exactly when
the logarithmic ratio across every reaction vanishes. -/
theorem entropyDissipation_sum_squares_eq_zero_iff (N : Network S) (κ : N.RateConstants)
    {x xstar : Concentration S} (hxs : xstar.Positive) :
    (∑ r : N.R, N.massActionRate κ r xstar * (N.reactionLogRatio x xstar r)^2) = 0
      ↔ ∀ r : N.R, N.reactionLogRatio x xstar r = 0 := by
  constructor
  · intro h r
    have hnonneg : ∀ r ∈ (Finset.univ : Finset N.R),
        0 ≤ N.massActionRate κ r xstar * (N.reactionLogRatio x xstar r)^2 := by
      intro r _
      exact mul_nonneg (N.massActionRate_pos κ r hxs).le (sq_nonneg _)
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp h
    have hz := hterm r (Finset.mem_univ r)
    have hsq : (N.reactionLogRatio x xstar r)^2 = 0 :=
      (mul_eq_zero.mp hz).resolve_left (N.massActionRate_pos κ r hxs).ne'
    exact sq_eq_zero_iff.mp hsq
  · intro h
    refine Finset.sum_eq_zero fun r _ => ?_
    rw [h r]
    simp

/-- **The entropy dissipation vanishes exactly at the complex-balanced states.** -/
theorem entropyDissipation_eq_zero_iff_complexBalanced (N : Network S) (κ : N.RateConstants)
    {x xstar : Concentration S} (hx : x.Positive) (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar) :
    N.relativeLogDissipation κ x xstar = 0 ↔ N.IsComplexBalanced κ x := by
  constructor
  · intro h
    exact complexBalanced_of_dissipation_eq_zero N κ hx hxs hcb h
  · intro h
    exact dissipation_eq_zero_of_complexBalanced N κ h

/-- **The remainder of the exponential expansion is nonnegative** (`exp u ≥ 1 + u`). -/
theorem complexLogRemainder_nonneg (N : Network S) {x xstar : Concentration S}
    (c : N.ComplexIdx) :
    0 ≤ N.complexLogRemainder x xstar c := by
  unfold complexLogRemainder
  have := Real.add_one_le_exp (N.complexLogRatio x xstar c)
  linarith

/-! ## The sum of squares along a trajectory -/

/-- **The sum-of-squares form of the derivative of the relative entropy.**

Along a mass-action trajectory, the rate of change of the relative entropy with respect to a
positive complex-balanced reference `x*` is the negative sum of squares of the logarithmic
ratios across the reactions, weighted by the equilibrium reaction fluxes, plus the explicit
remainder of `CRNT.Network.entropyDissipation_eq_sum_squares`. -/
theorem relEntropy_hasDerivAt_sum_squares (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} {γ : ℝ → Concentration S} {t : ℝ}
    (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    (hpos : (γ t).Positive)
    (hγ : ∀ s, HasDerivAt (fun τ => γ τ s) (N.massActionVectorField κ (γ t) s) t) :
    HasDerivAt (fun τ => relEntropy xstar (γ τ))
      (-(1 / 2 : ℝ) * ∑ r : N.R, N.massActionRate κ r xstar *
          (N.reactionLogRatio (γ t) xstar r)^2
        + ∑ r : N.R, N.massActionRate κ r xstar *
            N.complexLogRemainder (γ t) xstar (N.sourceIdx r) *
            N.reactionLogRatio (γ t) xstar r) t := by
  have h := relEntropy_hasDerivAt hxs hpos hγ
  have hd := entropyDissipation_eq_sum_squares N κ hpos hxs hcb
  unfold relativeLogDissipation at hd
  exact h.congr_deriv hd

/-! ## The worked instance: the reversible pair `A ⇌ B` -/

section ReversiblePair

open CRNT.Examples.ReversiblePair
open Species

/-- The two species of the reversible pair, as an explicit list. -/
theorem reversiblePair_sum_univ_species (f : Species → ℝ) : (∑ s : Species, f s) = f A + f B := by
  have huniv : (Finset.univ : Finset Species) = insert A {B} := by decide
  rw [huniv, Finset.sum_insert (by decide), Finset.sum_singleton]

/-- The mass-action vector field of the reversible pair at a positive state. -/
theorem reversiblePair_massActionVectorField (k₀ k₁ : ℝ) (h₀ : 0 < k₀) (h₁ : 0 < k₁)
    (x : Concentration Species) :
    N.massActionVectorField (rates h₀ h₁) x A = -(k₀ * x A) + k₁ * x B ∧
    N.massActionVectorField (rates h₀ h₁) x B = k₀ * x A - k₁ * x B := by
  have huniv : (Finset.univ : Finset Rxn) = insert Rxn.fwd {Rxn.bwd} := by decide
  have hvecbwd : N.reactionVector Rxn.bwd
      = fun s => match s with | A => (1 : ℝ) | B => -1 := by
    funext s
    cases s <;> simp [Network.reactionVector, N, rxn, Reaction.vector, cA, cB]
  have hmass : ∀ r : Rxn, N.massActionRate (rates h₀ h₁) r x
      = match r with | .fwd => k₀ * x A | .bwd => k₁ * x B := by
    intro r
    cases r with
    | fwd =>
        simp only [Network.massActionRate, rates, N, rxn, Complex.massActionMonomial, cA]
        rw [prod_univ_species]
        simp only [pow_one, pow_zero, mul_one]
    | bwd =>
        simp only [Network.massActionRate, rates, N, rxn, Complex.massActionMonomial, cB]
        rw [prod_univ_species]
        simp only [pow_one, pow_zero, one_mul]
  constructor
  · rw [Network.massActionVectorField_apply]
    show (∑ r : Rxn, N.massActionRate (rates h₀ h₁) r x * N.reactionVector r A)
        = -(k₀ * x A) + k₁ * x B
    rw [huniv, Finset.sum_insert (by decide), Finset.sum_singleton]
    have h1 : N.reactionVector Rxn.fwd A = (-1 : ℝ) := by
      rw [reactionVector_fwd]
    have h2 : N.reactionVector Rxn.bwd A = (1 : ℝ) := by
      rw [hvecbwd]
    rw [hmass Rxn.fwd, hmass Rxn.bwd, h1, h2]
    ring
  · rw [Network.massActionVectorField_apply]
    show (∑ r : Rxn, N.massActionRate (rates h₀ h₁) r x * N.reactionVector r B)
        = k₀ * x A - k₁ * x B
    rw [huniv, Finset.sum_insert (by decide), Finset.sum_singleton]
    have h1 : N.reactionVector Rxn.fwd B = (1 : ℝ) := by
      rw [reactionVector_fwd]
    have h2 : N.reactionVector Rxn.bwd B = (-1 : ℝ) := by
      rw [hvecbwd]
    rw [hmass Rxn.fwd, hmass Rxn.bwd, h1, h2]
    ring

/-- **Worked instance.**  For the reversible pair `A ⇌ B` with forward rate constant `k₀`
and backward rate constant `k₁`, the entropy dissipation relative to the detailed-balanced
equilibrium `x* = (k₁, k₀)` is the classical two-term expression

`(k₀ x_A − k₁ x_B) (log(k₁ x_B) − log(k₀ x_A))`,

which is nonpositive by the strict monotonicity of `log`. -/
theorem reversiblePair_entropyDissipation_eq_twoTerm (k₀ k₁ : ℝ) (h₀ : 0 < k₀) (h₁ : 0 < k₁)
    (x : Concentration Species) (hx : x.Positive) :
    N.relativeLogDissipation (rates h₀ h₁) x (equilibrium k₀ k₁)
      = (k₀ * x A - k₁ * x B) * (Real.log (k₁ * x B) - Real.log (k₀ * x A)) := by
  obtain ⟨hA, hB⟩ := reversiblePair_massActionVectorField k₀ k₁ h₀ h₁ x
  have hstarA : equilibrium k₀ k₁ A = k₁ := by rfl
  have hstarB : equilibrium k₀ k₁ B = k₀ := by rfl
  have hlog : Real.log (x A / equilibrium k₀ k₁ A) - Real.log (x B / equilibrium k₀ k₁ B)
      = Real.log (k₀ * x A) - Real.log (k₁ * x B) := by
    rw [hstarA, hstarB]
    rw [Real.log_div (hx A).ne' h₁.ne', Real.log_div (hx B).ne' h₀.ne',
      Real.log_mul h₀.ne' (hx A).ne', Real.log_mul h₁.ne' (hx B).ne']
    ring
  unfold relativeLogDissipation
  rw [reversiblePair_sum_univ_species, hA, hB, hstarA, hstarB]
  have h3 : Real.log (k₀ * x A) = Real.log k₀ + Real.log (x A) := by
    rw [Real.log_mul h₀.ne' (hx A).ne']
  have h4 : Real.log (k₁ * x B) = Real.log k₁ + Real.log (x B) := by
    rw [Real.log_mul h₁.ne' (hx B).ne']
  rw [h3, h4]
  ring

/-- **The two-term dissipation is nonpositive**, i.e. the Gibbs bound for the reversible
pair. -/
theorem reversiblePair_entropyDissipation_nonpos (k₀ k₁ : ℝ) (h₀ : 0 < k₀) (h₁ : 0 < k₁)
    (x : Concentration Species) (hx : x.Positive) :
    N.relativeLogDissipation (rates h₀ h₁) x (equilibrium k₀ k₁) ≤ 0 := by
  have hcb := equilibrium_isComplexBalanced h₀ h₁
  have hxs := equilibrium_positive h₀ h₁
  have hd := dissipation_nonpos N (rates h₀ h₁) hx hxs hcb
  simpa [relativeLogDissipation] using hd

end ReversiblePair

/-! ## The naive Horn–Jackson identity is false -/

/-- The naive Horn–Jackson sum of squares: the forward flux of each reaction weighted by the
square of the pairing of its reaction vector with the *entropy-Hessian-scaled* logarithmic
ratio `D(x*)⁻¹ log(x/x*)`.  The identity
`d/dt G = −(1/2) ∑_r q_r(x) ⟨ν_r, D(x*)⁻¹ h⟩²` would force this quantity to be
`−d/dt G`. -/
noncomputable def naiveLogSumSquares (N : Network S) (κ : N.RateConstants)
    (x xstar : Concentration S) : ℝ :=
  ∑ r : N.R, N.massActionRate κ r x *
    (∑ s, N.reactionVector r s *
      ((Real.log (x s) - Real.log (xstar s)) / xstar s))^2

section NaiveIdentity

open CRNT.Examples.ReversiblePair
open Species

/-- A positive complex-balanced reference of the reversible pair with unit rate constants:
`x* = (2, 2)`.  (For unit rate constants the complex-balanced references are exactly the
diagonal ones.) -/
def reversiblePair_naiveReference : Concentration Species := fun _ => 2

/-- A positive state of the reversible pair: `x = (4, 2)`. -/
def reversiblePair_naiveState : Concentration Species := fun s => match s with | A => 4 | B => 2

/-- **The naive Horn–Jackson identity is false.**

For the reversible pair `A ⇌ B` with unit rate constants, the complex-balanced reference
`x* = (2, 2)` and the state `x = (4, 2)`, the naive sum of squares
`∑_r q_r(x) ⟨ν_r, D(x*)⁻¹ log(x/x*)⟩²` is `3/2 (log 2)²`, whereas the entropy dissipation
`−⟨log(x/x*), f(x)⟩` is `4 log 2`.  The two are unequal: equality would force
`log 2 = 8/3`, whereas `log 2 < 1`. -/
theorem reversiblePair_naiveIdentity_fails (hunit₀ hunit₁ : (0 : ℝ) < 1) :
    N.naiveLogSumSquares (rates hunit₀ hunit₁) reversiblePair_naiveState reversiblePair_naiveReference
      ≠ -2 * N.relativeLogDissipation (rates hunit₀ hunit₁) reversiblePair_naiveState reversiblePair_naiveReference := by
  have hlog2 : Real.log (2 : ℝ) < 1 := by
    have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)
    linarith
  have hlog4 : Real.log (4 : ℝ) - Real.log (2 : ℝ) = Real.log (2 : ℝ) := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
    ring
  have hinner (r : Rxn) :
      (∑ s : Species, N.reactionVector r s *
        ((Real.log (reversiblePair_naiveState s) - Real.log (reversiblePair_naiveReference s)) / reversiblePair_naiveReference s))
        = if r = Rxn.fwd then -(Real.log (2 : ℝ)) / 2 else (Real.log (2 : ℝ)) / 2 := by
    cases r with
    | fwd =>
        rw [reversiblePair_sum_univ_species]
        simp only [reversiblePair_naiveState, reversiblePair_naiveReference]
        rw [reactionVector_fwd]
        simp only
        rw [hlog4]
        simp
        ring
    | bwd =>
        rw [reversiblePair_sum_univ_species]
        simp only [reversiblePair_naiveState, reversiblePair_naiveReference]
        have hvec : N.reactionVector Rxn.bwd
            = fun s => match s with | A => (1 : ℝ) | B => -1 := by
          funext s
          cases s <;> simp [Network.reactionVector, N, rxn, Reaction.vector, cA, cB]
        rw [hvec]
        simp only
        rw [hlog4]
        simp
  have hrates : ∀ r : Rxn, N.massActionRate (rates hunit₀ hunit₁) r reversiblePair_naiveState
      = match r with | .fwd => (4 : ℝ) | .bwd => 2 := by
    intro r
    cases r with
    | fwd =>
        simp only [rates, Network.massActionRate, N, rxn,
          Complex.massActionMonomial, cA, reversiblePair_naiveState]
        rw [prod_univ_species]
        simp only [pow_one, pow_zero]
        ring
    | bwd =>
        simp only [rates, Network.massActionRate, N, rxn,
          Complex.massActionMonomial, cB, reversiblePair_naiveState]
        rw [prod_univ_species]
        simp only [pow_one, pow_zero, one_mul]
  have hfield : ∀ s : Species, N.massActionVectorField (rates hunit₀ hunit₁) reversiblePair_naiveState s
      = match s with | A => (-2 : ℝ) | B => 2 := by
    intro s
    obtain ⟨hA, hB⟩ :=
      reversiblePair_massActionVectorField 1 1 hunit₀ hunit₁ reversiblePair_naiveState
    cases s with
    | A => rw [hA]; simp only [reversiblePair_naiveState]; ring
    | B => rw [hB]; simp only [reversiblePair_naiveState]; ring
  have hdiss : N.relativeLogDissipation (rates hunit₀ hunit₁) reversiblePair_naiveState reversiblePair_naiveReference
      = -2 * Real.log (2 : ℝ) := by
    unfold relativeLogDissipation
    rw [reversiblePair_sum_univ_species, hfield Species.A, hfield Species.B]
    simp only [reversiblePair_naiveState, reversiblePair_naiveReference]
    rw [hlog4]
    ring
  -- the naive sum of squares is `3/2 (log 2)^2`
  have hnaive : N.naiveLogSumSquares (rates hunit₀ hunit₁) reversiblePair_naiveState reversiblePair_naiveReference
      = (3 / 2 : ℝ) * (Real.log (2 : ℝ))^2 := by
    unfold naiveLogSumSquares
    have huniv : (Finset.univ : Finset Rxn) = insert Rxn.fwd {Rxn.bwd} := by decide
    show (∑ r : Rxn, N.massActionRate (rates hunit₀ hunit₁) r reversiblePair_naiveState *
      (∑ s : Species, N.reactionVector r s *
        ((Real.log (reversiblePair_naiveState s) - Real.log (reversiblePair_naiveReference s)) / reversiblePair_naiveReference s))^2)
        = (3 / 2 : ℝ) * (Real.log (2 : ℝ))^2
    rw [huniv, Finset.sum_insert (by decide), Finset.sum_singleton]
    rw [hrates Rxn.fwd, hrates Rxn.bwd, hinner Rxn.fwd, hinner Rxn.bwd]
    simp
    ring
  rw [hnaive, hdiss]
  intro h
  have hlog2pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  nlinarith

end NaiveIdentity

/-! ## Axiom audit of the principal declarations -/

#print axioms CRNT.Network.complexLogRatio_eq_pairing
#print axioms CRNT.Network.reactionLogRatio_eq_pairing
#print axioms CRNT.Network.entropyDissipation_eq_fluxLogRatio
#print axioms CRNT.Network.complexBalance_fluxBalance
#print axioms CRNT.Network.entropyDissipation_eq_eqFluxLogRatio
#print axioms CRNT.Network.entropyDissipation_eq_sum_squares
#print axioms CRNT.Network.entropyDissipation_sum_squares_nonneg
#print axioms CRNT.Network.entropyDissipation_sum_squares_eq_zero_iff
#print axioms CRNT.Network.entropyDissipation_eq_zero_iff_complexBalanced
#print axioms CRNT.Network.complexLogRemainder_nonneg
#print axioms CRNT.Network.relEntropy_hasDerivAt_sum_squares
#print axioms CRNT.Network.reversiblePair_entropyDissipation_eq_twoTerm
#print axioms CRNT.Network.reversiblePair_entropyDissipation_nonpos
#print axioms CRNT.Network.reversiblePair_naiveIdentity_fails

end Network

end CRNT
