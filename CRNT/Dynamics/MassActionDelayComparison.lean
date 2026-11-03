import CRNT.Kinetics.MassActionJacobian
import CRNT.Stochastic.KurtzFluidLimit
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Local Lipschitz bounds for mass-action fields and delay-system scope

This module proves an *explicit* Lipschitz bound for the mass-action vector field of a chemical
reaction network on every bounded ball. This bound is useful for local well-posedness and
Gronwall estimates. It does not prove a comparison principle for mass-action delay equations;
the comparison boundary is described below.

## The mass-action field and its derivative

For a network `N` with rate constants `κ` the mass-action vector field is

`F(x) = ∑_r κ_r · x^{y_r} · (y'_r − y_r)`,

a polynomial map of the concentration vector `x ∈ Concentration S = S → ℝ`.  Its Fréchet
derivative is the mass-action Jacobian `N.massActionJacobianCLM κ x`, whose `j`-th column is
built from the gradient of the source monomials,

`∂_j x^{y_r} = y_{r,j} · x_j^{y_{r,j} − 1} · ∏_{s ≠ j} x_s^{y_{r,s}}`.

The bound proved here is the classical **local Lipschitz estimate for polynomial vector
fields**: on the ball of radius `B` around the origin the operator norm of the derivative is
bounded by

`K(B) = ∑_r κ_r · deg(r) · (B + 1)^{deg(r)} · ‖y'_r − y_r‖`,

where `deg(r) = ∑_s y_{r,s}` is the degree of the source complex of reaction `r`.  The factor
`(B + 1)^{deg r}` is the standard "polynomial growth" estimate: a monomial of degree `d` has
derivative of size `≤ B^{d−1}` on the ball of radius `B`, and `B + 1` avoids the case `B < 1`.

Reference: the standard local Lipschitz estimate for polynomial ODEs (Hale, *Ordinary
Differential Equations*, Wiley 1980, Ch. 1); the mass-action field itself is the classical
CRN vector field of Craciun (2006), Feinberg (1979) and Shiu (2000).

## What is proved here

* `sourceDegree`: the degree of the source complex of a reaction;
* `massActionLipschitzConstant`: the explicit constant `K(B)` above;
* `massActionVectorField_fderiv`: the Fréchet derivative of the mass-action field is the
  mass-action Jacobian;
* `abs_massActionMonomialGrad_le`: the entrywise bound on the gradient of a source monomial;
* `sum_abs_massActionMonomialGrad_le`: the corresponding bound on the whole gradient;
* `massActionJacobianCLM_apply_sum_coordinate`: the Jacobian operator in coordinate form;
* `massActionJacobianCLM_norm_le`: the operator-norm bound `‖Df(x)‖ ≤ K(B)` on the ball;
* `massActionVectorField_nnnorm_fderiv_le`: the same bound in the `NNNorm` form
  `‖fderiv ℝ F x‖₊ ≤ K(B)` that the repository's conditional Lipschitz step consumes;
* `massActionVectorField_lipschitzOnWith_closedBall`: **the mass-action field is Lipschitz on
  every bounded ball**, with the explicit constant `K(B)`.

## The comparison principle: scope and boundary

The general componentwise comparison principle does not hold for all mass-action delay systems
`ẋ(t) = ∑_r κ_r (x(t − τ_r)^{y_r} y'_r − x(t)^{y_r} y_r)`, as the following example shows.

On the nonnegative orthant, a consumption term can contribute nonpositive off-diagonal
derivatives in the current state when a reaction consumes multiple species. Those terms can
violate the Kamke condition; delayed production terms alone do not imply cooperativity. The
repository formalizes one such obstruction in
`CRNT.Network.twoSpeciesDegradation_not_massActionKamkeOn`
(`CRNT/Dynamics/DelayComparisonLattice.lean`).

The **counterexample** is the two-species degradation network `A + B → ∅` (`κ = 1`, any delay
`τ ≥ 0`), whose delay system reads `ẋ = −x_A x_B`. The two solutions

`x(t) = (1/(1+t), 1/(1+t))`  and  `y(t) = (e^{−t}/(2 − e^{−t}), 1 + e^{−t}/(2 − e^{−t}))`

satisfy `x(0) = (1,1) ≤ (1,2) = y(0)`, but `x_A(1) = 1/2 > e^{−1}/(2 − e^{−1}) = y_A(1)`:
the order is destroyed. (Both are solutions because `d/dt (u − v) = 0` along solutions of
`u' = −uv`, `v' = −uv`.) *This counterexample is stated analytically here; it is not yet
machine-checked in the repository.*

The comparison principle in `CRNT/Dynamics/DelayComparisonLattice.lean` applies to cooperative
delay fields. Monomolecular mass-action fields are one useful class covered by that hypothesis;
this module does not classify all mass-action networks whose fields are cooperative. General
mass-action delay fields need not satisfy Kamke, as the degradation example above shows. The
explicit local Lipschitz estimate proved here is available for future arguments, but is not
itself a comparison result.

## The Lyapunov function

The Lyapunov–Krasovskii functional of Lipták–Hangos–Pituk–Szederkényi for the mass-action
delay systems is `CRNT.Network.delayLyapunov`, and the two results
`CRNT.Network.delayLyapunov_hasDerivAt` and `CRNT.Network.delayLyapunov_deriv_nonpos`
(`CRNT/Extensions/DelayLyapunov.lean`) already establish that it is nonincreasing along the
solutions of the mass-action delay system (`CRNT.Network.delayLyapunov_antitone`). The local
Lipschitz estimate in this module concerns the undelayed vector field
`N.massActionVectorField κ`. It is an additional bound that can support ODE uniqueness and
Gronwall arguments; it does not assert a Lipschitz bound for the full delay field or extend the
delay comparison theorem.

Depends on: `CRNT.Kinetics.MassActionJacobian`, `CRNT.Stochastic.KurtzFluidLimit`.
-/

namespace CRNT

namespace Network

open scoped BigOperators
open Filter Topology Set

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ### The explicit Lipschitz constant of the mass-action field -/

omit [Fintype S] in
/-- **A product of powers bounded by a common base.**  If `|x_s| ≤ B` for all `s ∈ E` then
`∏_{s ∈ E} |x_s|^{n_s} ≤ B^{∑_{s ∈ E} n_s}`. -/
private lemma prod_abs_pow_le (B : ℝ) (E : Finset S) (n : S → ℕ) (hB : 0 ≤ B)
    (x : Concentration S) :
    (∀ s ∈ E, |x s| ≤ B) → (∏ s ∈ E, |x s| ^ (n s)) ≤ B ^ (∑ s ∈ E, n s) := by
  induction E using Finset.induction_on with
  | empty => intro _; simp
  | @insert a E ha ih =>
      intro hx
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      have h1 : |x a| ^ (n a) ≤ B ^ (n a) :=
        pow_le_pow_left₀ (abs_nonneg _) (hx a (Finset.mem_insert_self a E)) (n a)
      have h2 : (∏ s ∈ E, |x s| ^ (n s)) ≤ B ^ (∑ s ∈ E, n s) :=
        ih (fun s hs => hx s (Finset.mem_insert_of_mem hs))
      calc |x a| ^ (n a) * (∏ s ∈ E, |x s| ^ (n s))
          ≤ B ^ (n a) * B ^ (∑ s ∈ E, n s) :=
            mul_le_mul h1 h2 (Finset.prod_nonneg fun s _ => pow_nonneg (abs_nonneg _) _)
              (pow_nonneg hB _)
        _ = B ^ (n a + ∑ s ∈ E, n s) := by rw [pow_add]

omit [Fintype S] in
/-- **A product of powers of a common base is the power of the sum of the exponents.** -/
private lemma prod_pow_eq_pow_sum (B : ℝ) (E : Finset S) (n : S → ℕ) :
    (∏ s ∈ E, B ^ (n s)) = B ^ (∑ s ∈ E, n s) := by
  induction E using Finset.induction_on with
  | empty => simp
  | @insert a E ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, ← pow_add]

/-- **The degree of the source complex of a reaction.**  For a reaction `r` with source complex
`y_r`, this is `∑_s y_{r,s}`, the total number of reactant molecules; it is the degree of the
mass-action monomial `x^{y_r}` and hence the degree of the polynomial `x ↦ x^{y_r}`. -/
def sourceDegree (N : Network S) (r : N.R) : ℕ :=
  ∑ s, (N.reaction r).source s

/-- **An explicit Lipschitz constant for the mass-action vector field on a ball of radius `B`.**

The constant is

`K(B) = ∑_r κ_r · deg(r) · (B + 1)^{deg(r)} · ‖y'_r − y_r‖`,

with `deg(r)` the degree of the source complex of reaction `r`.  The factor
`(B + 1)^{deg(r)}` is the standard polynomial-growth estimate: the derivative of a monomial
of degree `d` is bounded by `B^{d−1}` on the ball of radius `B`, and `B + 1` is used to avoid
the separate treatment of `B < 1`. -/
def massActionLipschitzConstant (N : Network S) (κ : N.RateConstants) (B : ℝ) : ℝ :=
  ∑ r : N.R, κ.k r * ((sourceDegree N r : ℝ) * (B + 1) ^ (sourceDegree N r)) *
    ‖N.reactionVector r‖

/-- The Lipschitz constant is nonnegative. -/
theorem massActionLipschitzConstant_nonneg (N : Network S) (κ : N.RateConstants) (B : ℝ)
    (hB : 0 ≤ B) : 0 ≤ massActionLipschitzConstant N κ B := by
  refine Finset.sum_nonneg fun r _ => ?_
  have h1 : 0 ≤ κ.k r := (κ.positive r).le
  have h2 : 0 ≤ (sourceDegree N r : ℝ) := Nat.cast_nonneg _
  have h3 : 0 ≤ (B + 1) ^ (sourceDegree N r) := by positivity
  have h4 : 0 ≤ ‖N.reactionVector r‖ := norm_nonneg _
  positivity

/-- **The Fréchet derivative of the mass-action field is the mass-action Jacobian.** -/
theorem massActionVectorField_fderiv (N : Network S) (κ : N.RateConstants)
    (x : Concentration S) :
    fderiv ℝ (N.massActionVectorField κ) x = N.massActionJacobianCLM κ x := by
  exact (N.massActionVectorField_hasFDerivAt κ x).fderiv

/-- **Entrywise bound on the gradient of a source monomial.**  For `y` a complex and `x` a
concentration with `|x_s| ≤ B` for all `s`,

`|∂_j x^{y}| ≤ y_j · (B + 1)^{∑_s y_s}`.

Indeed, `∂_j x^y = y_j · x_j^{y_j − 1} · ∏_{s ≠ j} x_s^{y_s}`, and on the ball of radius `B`
every factor `x_s^{y_s}` is bounded by `B^{y_s}`; the product is bounded by
`B^{∑_s y_s − 1} ≤ (B + 1)^{∑_s y_s}`. -/
theorem abs_massActionMonomialGrad_le {y : Complex S} {x : Concentration S} {j : S} {B : ℝ}
    (hB : 0 ≤ B) (hx : ∀ s, |x s| ≤ B) :
    |massActionMonomialGrad y x j| ≤ (y j : ℝ) * (B + 1) ^ (∑ s, y s) := by
  have hgrad : massActionMonomialGrad y x j
      = (y j : ℝ) * x j ^ (y j - 1) * ∏ s ∈ Finset.univ.erase j, x s ^ (y s) := rfl
  have hprod : |∏ s ∈ Finset.univ.erase j, x s ^ (y s)|
      = ∏ s ∈ Finset.univ.erase j, |x s| ^ (y s) := by
    rw [Finset.abs_prod]
    exact Finset.prod_congr rfl fun s _ => abs_pow _ _
  have hpow : |x j| ^ (y j - 1) ≤ B ^ (y j - 1) :=
    pow_le_pow_left₀ (abs_nonneg _) (hx j) (y j - 1)
  have hprod' : (∏ s ∈ Finset.univ.erase j, |x s| ^ (y s))
      ≤ B ^ (∑ s ∈ Finset.univ.erase j, y s) :=
    prod_abs_pow_le B (Finset.univ.erase j) y hB x (fun s _ => hx s)
  have hsum : (∑ s ∈ Finset.univ.erase j, y s) + y j = ∑ s, y s := by
    have := Finset.sum_erase_add Finset.univ (fun s : S => y s) (Finset.mem_univ j)
    simpa using this
  have hexp : y j - 1 + ∑ s ∈ Finset.univ.erase j, y s ≤ ∑ s, y s := by omega
  have hpow' : B ^ (y j - 1 + ∑ s ∈ Finset.univ.erase j, y s)
      ≤ (B + 1) ^ (∑ s, y s) := by
    have h1 : B ^ (y j - 1 + ∑ s ∈ Finset.univ.erase j, y s)
        ≤ (B + 1) ^ (y j - 1 + ∑ s ∈ Finset.univ.erase j, y s) :=
      pow_le_pow_left₀ (by linarith) (by linarith) _
    have h2 : (B + 1) ^ (y j - 1 + ∑ s ∈ Finset.univ.erase j, y s)
        ≤ (B + 1) ^ (∑ s, y s) := pow_le_pow_right₀ (by linarith) hexp
    exact h1.trans h2
  have hnonneg : 0 ≤ ∏ s ∈ Finset.univ.erase j, |x s| ^ (y s) :=
    Finset.prod_nonneg fun s _ => pow_nonneg (abs_nonneg _) _
  calc |massActionMonomialGrad y x j|
      = (y j : ℝ) * |x j| ^ (y j - 1) * ∏ s ∈ Finset.univ.erase j, |x s| ^ (y s) := by
        rw [hgrad, abs_mul, abs_mul, hprod, abs_pow, abs_of_nonneg (Nat.cast_nonneg (y j))]
    _ ≤ (y j : ℝ) * B ^ (y j - 1) * ∏ s ∈ Finset.univ.erase j, |x s| ^ (y s) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg (y j))) hnonneg
    _ ≤ (y j : ℝ) * B ^ (y j - 1) * B ^ (∑ s ∈ Finset.univ.erase j, y s) :=
        mul_le_mul_of_nonneg_left hprod'
          (mul_nonneg (Nat.cast_nonneg (y j)) (pow_nonneg hB _))
    _ = (y j : ℝ) * B ^ (y j - 1 + ∑ s ∈ Finset.univ.erase j, y s) := by
        have h : B ^ (y j - 1 + ∑ s ∈ Finset.univ.erase j, y s)
            = B ^ (y j - 1) * B ^ (∑ s ∈ Finset.univ.erase j, y s) := pow_add _ _ _
        rw [h]
        ring
    _ ≤ (y j : ℝ) * (B + 1) ^ (∑ s, y s) :=
        mul_le_mul_of_nonneg_left hpow' (Nat.cast_nonneg (y j))

/-- **The sum of the absolute values of the gradient entries of a source monomial.** -/
theorem sum_abs_massActionMonomialGrad_le {y : Complex S} {x : Concentration S} {B : ℝ}
    (hB : 0 ≤ B) (hx : ∀ s, |x s| ≤ B) :
    (∑ j : S, |massActionMonomialGrad y x j|)
      ≤ (∑ j : S, (y j : ℝ)) * (B + 1) ^ (∑ s, y s) := by
  calc (∑ j : S, |massActionMonomialGrad y x j|)
      ≤ ∑ j : S, (y j : ℝ) * (B + 1) ^ (∑ s, y s) := by
        refine Finset.sum_le_sum fun j _ => abs_massActionMonomialGrad_le hB hx
    _ = (B + 1) ^ (∑ s, y s) * ∑ j : S, (y j : ℝ) := by
        have h1 : (∑ j : S, (y j : ℝ) * (B + 1) ^ (∑ s, y s))
            = ∑ j : S, (B + 1) ^ (∑ s, y s) * (y j : ℝ) := by
          exact Finset.sum_congr rfl fun j _ => by ring
        rw [h1, ← Finset.mul_sum]
    _ = (∑ j : S, (y j : ℝ)) * (B + 1) ^ (∑ s, y s) := by ring

/-- **The Jacobian operator, written out.** -/
theorem massActionJacobianCLM_apply_sum_coordinate (N : Network S) (κ : N.RateConstants)
    (x u : Concentration S) (s : S) :
    N.massActionJacobianCLM κ x u s
      = ∑ r : N.R, κ.k r * (∑ j : S, massActionMonomialGrad (N.reaction r).source x j * u j) *
          N.reactionVector r s := by
  rw [massActionJacobianCLM_apply, Matrix.mulVec_apply_eq_sum]
  simp only [massActionJacobian]
  have h1 : (∑ j : S, (∑ r : N.R, κ.k r *
        massActionMonomialGrad (N.reaction r).source x j * N.reactionVector r s) * u j)
      = ∑ j : S, ∑ r : N.R, κ.k r * massActionMonomialGrad (N.reaction r).source x j *
        N.reactionVector r s * u j := by
    refine Finset.sum_congr rfl fun j _ => ?_
    exact Finset.sum_mul Finset.univ _ _
  have hswap : (∑ j : S, ∑ r : N.R, κ.k r *
        massActionMonomialGrad (N.reaction r).source x j * N.reactionVector r s * u j)
      = ∑ r : N.R, ∑ j : S, κ.k r * massActionMonomialGrad (N.reaction r).source x j *
        N.reactionVector r s * u j :=
    Finset.sum_comm (f := fun j r => κ.k r *
      massActionMonomialGrad (N.reaction r).source x j * N.reactionVector r s * u j)
  rw [h1, hswap]
  refine Finset.sum_congr rfl fun r _ => ?_
  calc (∑ j : S, κ.k r * massActionMonomialGrad (N.reaction r).source x j *
          N.reactionVector r s * u j)
      = ∑ j : S, κ.k r * ((massActionMonomialGrad (N.reaction r).source x j * u j) *
          N.reactionVector r s) := by
        exact Finset.sum_congr rfl fun j _ => by ring
    _ = κ.k r * ∑ j : S, (massActionMonomialGrad (N.reaction r).source x j * u j) *
          N.reactionVector r s :=
        (Finset.mul_sum Finset.univ (fun j : S =>
          (massActionMonomialGrad (N.reaction r).source x j * u j) * N.reactionVector r s)
          (κ.k r)).symm
    _ = κ.k r * ((∑ j : S, massActionMonomialGrad (N.reaction r).source x j * u j) *
          N.reactionVector r s) := by
        rw [(Finset.sum_mul Finset.univ (fun j : S =>
          massActionMonomialGrad (N.reaction r).source x j * u j) (N.reactionVector r s)).symm]
    _ = κ.k r * (∑ j : S, massActionMonomialGrad (N.reaction r).source x j * u j) *
          N.reactionVector r s := by ring

/-- **The sharp Lipschitz constant of the mass-action Jacobian at `x`.**  This is the
`x`-dependent constant; `massActionLipschitzConstant` bounds it in terms of the radius of a
ball containing `x`. -/
def massActionJacobianConstant (N : Network S) (κ : N.RateConstants) (x : Concentration S) : ℝ :=
  ∑ r : N.R, κ.k r * (∑ j : S, |massActionMonomialGrad (N.reaction r).source x j|) *
    ‖N.reactionVector r‖

/-- The Jacobian constant is nonnegative. -/
theorem massActionJacobianConstant_nonneg (N : Network S) (κ : N.RateConstants)
    (x : Concentration S) : 0 ≤ massActionJacobianConstant N κ x := by
  unfold massActionJacobianConstant
  refine Finset.sum_nonneg fun r _ => ?_
  have h1 : 0 ≤ κ.k r := (κ.positive r).le
  have h2 : 0 ≤ ∑ j : S, |massActionMonomialGrad (N.reaction r).source x j| :=
    Finset.sum_nonneg fun j _ => abs_nonneg _
  have h3 : 0 ≤ ‖N.reactionVector r‖ := norm_nonneg _
  positivity

/-- **The operator-norm bound for the mass-action Jacobian.**  For every `x` and every `u`,

`‖Df(x) u‖ ≤ K(x) ‖u‖`,

with `K(x) = massActionJacobianConstant N κ x`. -/
theorem massActionJacobianCLM_norm_le_aux (N : Network S) (κ : N.RateConstants)
    (x u : Concentration S) :
    ‖N.massActionJacobianCLM κ x u‖ ≤ massActionJacobianConstant N κ x * ‖u‖ := by
  have hnorm : ∀ j : S, |u j| ≤ ‖u‖ := by
    intro j
    have h := norm_le_pi_norm u j
    rw [Real.norm_eq_abs] at h
    exact h
  have hinner : ∀ r : N.R,
      |∑ j : S, massActionMonomialGrad (N.reaction r).source x j * u j|
        ≤ (∑ j : S, |massActionMonomialGrad (N.reaction r).source x j|) * ‖u‖ := by
    intro r
    calc |∑ j : S, massActionMonomialGrad (N.reaction r).source x j * u j|
        ≤ ∑ j : S, |massActionMonomialGrad (N.reaction r).source x j * u j| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : S, |massActionMonomialGrad (N.reaction r).source x j| * ‖u‖ := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hnorm j) (abs_nonneg _)
      _ = (∑ j : S, |massActionMonomialGrad (N.reaction r).source x j|) * ‖u‖ :=
          (Finset.sum_mul Finset.univ _ _).symm
  have hcomp : ∀ s : S,
      |N.massActionJacobianCLM κ x u s| ≤ massActionJacobianConstant N κ x * ‖u‖ := by
    intro s
    rw [massActionJacobianCLM_apply_sum_coordinate]
    calc |∑ r : N.R, κ.k r * (∑ j : S,
            massActionMonomialGrad (N.reaction r).source x j * u j) * N.reactionVector r s|
        ≤ ∑ r : N.R, |κ.k r * (∑ j : S,
            massActionMonomialGrad (N.reaction r).source x j * u j) * N.reactionVector r s| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ r : N.R, κ.k r * |∑ j : S,
            massActionMonomialGrad (N.reaction r).source x j * u j| * |N.reactionVector r s| := by
          refine Finset.sum_le_sum fun r _ => ?_
          have h1 : |κ.k r * (∑ j : S,
                massActionMonomialGrad (N.reaction r).source x j * u j) * N.reactionVector r s|
              = κ.k r * |∑ j : S,
                massActionMonomialGrad (N.reaction r).source x j * u j| *
                  |N.reactionVector r s| := by
            rw [abs_mul, abs_mul, abs_of_nonneg (κ.positive r).le]
          rw [h1]
      _ ≤ ∑ r : N.R, (κ.k r * (∑ j : S,
            |massActionMonomialGrad (N.reaction r).source x j|)) * ‖N.reactionVector r‖ * ‖u‖ := by
          refine Finset.sum_le_sum fun r _ => ?_
          have h2 : κ.k r * |∑ j : S, massActionMonomialGrad (N.reaction r).source x j * u j|
              ≤ κ.k r * ((∑ j : S, |massActionMonomialGrad (N.reaction r).source x j|) * ‖u‖) :=
            mul_le_mul_of_nonneg_left (hinner r) (κ.positive r).le
          have h3 : |N.reactionVector r s| ≤ ‖N.reactionVector r‖ := by
            have h := norm_le_pi_norm (N.reactionVector r) s
            rw [Real.norm_eq_abs] at h
            exact h
          have h4 : κ.k r * ((∑ j : S,
                |massActionMonomialGrad (N.reaction r).source x j|) * ‖u‖) *
                |N.reactionVector r s|
              ≤ κ.k r * ((∑ j : S,
                |massActionMonomialGrad (N.reaction r).source x j|) * ‖u‖) *
                ‖N.reactionVector r‖ :=
            mul_le_mul_of_nonneg_left h3 (mul_nonneg (κ.positive r).le
              (mul_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg _) (norm_nonneg u)))
          have h5 : κ.k r * |∑ j : S,
                massActionMonomialGrad (N.reaction r).source x j * u j| *
                |N.reactionVector r s|
              ≤ κ.k r * ((∑ j : S,
                |massActionMonomialGrad (N.reaction r).source x j|) * ‖u‖) *
                |N.reactionVector r s| := mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
          calc κ.k r * |∑ j : S,
                massActionMonomialGrad (N.reaction r).source x j * u j| *
                |N.reactionVector r s|
              ≤ κ.k r * ((∑ j : S,
                |massActionMonomialGrad (N.reaction r).source x j|) * ‖u‖) *
                |N.reactionVector r s| := h5
            _ ≤ κ.k r * ((∑ j : S,
                |massActionMonomialGrad (N.reaction r).source x j|) * ‖u‖) *
                ‖N.reactionVector r‖ := h4
            _ = (κ.k r * (∑ j : S,
                |massActionMonomialGrad (N.reaction r).source x j|)) *
                ‖N.reactionVector r‖ * ‖u‖ := by ring
      _ = massActionJacobianConstant N κ x * ‖u‖ := by
          unfold massActionJacobianConstant
          rw [(Finset.sum_mul Finset.univ (fun r : N.R => κ.k r * (∑ j : S,
                |massActionMonomialGrad (N.reaction r).source x j|) *
                ‖N.reactionVector r‖) ‖u‖)]
  have hpi : ∀ i : S, ‖(N.massActionJacobianCLM κ x u) i‖
      ≤ massActionJacobianConstant N κ x * ‖u‖ := by
    intro s
    rw [Real.norm_eq_abs]
    exact hcomp s
  exact (pi_norm_le_iff_of_nonneg (G := fun _ : S => ℝ)
    (x := N.massActionJacobianCLM κ x u)
    (mul_nonneg (massActionJacobianConstant_nonneg N κ x) (norm_nonneg u))).mpr hpi

/-- **The Jacobian constant is bounded by the explicit constant of the ball.**  If `‖x‖ ≤ B`
then `K(x) ≤ K(B) = massActionLipschitzConstant N κ B`. -/
theorem massActionJacobianConstant_le (N : Network S) (κ : N.RateConstants)
    (B : ℝ) (x : Concentration S) (hx : ‖x‖ ≤ B) :
    massActionJacobianConstant N κ x ≤ massActionLipschitzConstant N κ B := by
  have hB : 0 ≤ B := le_trans (norm_nonneg x) hx
  have hxs : ∀ s, |x s| ≤ B := by
    intro s
    have h1 : ‖x s‖ ≤ ‖x‖ := norm_le_pi_norm x s
    have h2 : |x s| ≤ B := by
      rw [← Real.norm_eq_abs]
      exact h1.trans hx
    exact h2
  unfold massActionJacobianConstant massActionLipschitzConstant
  refine Finset.sum_le_sum fun r _ => ?_
  have h1 : (∑ j : S, |massActionMonomialGrad (N.reaction r).source x j|)
      ≤ (sourceDegree N r : ℝ) * (B + 1) ^ (sourceDegree N r) := by
    have hdeg : (∑ j : S, ((N.reaction r).source j : ℝ)) = (sourceDegree N r : ℝ) := by
      rw [sourceDegree]
      exact_mod_cast (Finset.sum_congr rfl fun s _ => rfl)
    rw [← hdeg]
    exact sum_abs_massActionMonomialGrad_le hB hxs
  have h2 : κ.k r * (∑ j : S, |massActionMonomialGrad (N.reaction r).source x j|)
      ≤ κ.k r * ((sourceDegree N r : ℝ) * (B + 1) ^ (sourceDegree N r)) :=
    mul_le_mul_of_nonneg_left h1 (κ.positive r).le
  exact mul_le_mul_of_nonneg_right h2 (norm_nonneg (N.reactionVector r))

/-- **The operator-norm bound for the mass-action Jacobian on the ball of radius `B`.**  For
every `x` with `‖x‖ ≤ B` and every `u`,

`‖Df(x) u‖ ≤ K(B) ‖u‖`,

with `K(B) = massActionLipschitzConstant N κ B`. -/
theorem massActionJacobianCLM_norm_le (N : Network S) (κ : N.RateConstants)
    (B : ℝ) (x u : Concentration S) (hx : ‖x‖ ≤ B) :
    ‖N.massActionJacobianCLM κ x u‖ ≤ massActionLipschitzConstant N κ B * ‖u‖ := by
  have h := massActionJacobianCLM_norm_le_aux N κ x u
  exact le_trans h (mul_le_mul_of_nonneg_right
    (massActionJacobianConstant_le N κ B x hx) (norm_nonneg u))

/-- **The derivative of the mass-action field is bounded, in operator norm, on every ball.**
For `‖x‖ ≤ B`,

`‖fderiv ℝ (N.massActionVectorField κ) x‖₊ ≤ K(B)`,

with `K(B) = massActionLipschitzConstant N κ B` the explicit constant above.  This is the
hypothesis consumed by `CRNT.Network.massActionVectorField_lipschitzOnWith_of_fderiv_le`. -/
theorem massActionVectorField_nnnorm_fderiv_le (N : Network S) (κ : N.RateConstants)
    (B : ℝ) (x : Concentration S) (hx : ‖x‖ ≤ B) :
    ‖fderiv ℝ (N.massActionVectorField κ) x‖₊
      ≤ Real.toNNReal (massActionLipschitzConstant N κ B) := by
  have hB : 0 ≤ B := le_trans (norm_nonneg x) hx
  have hC : 0 ≤ massActionLipschitzConstant N κ B :=
    massActionLipschitzConstant_nonneg N κ B hB
  -- the Jacobian is Lipschitz with the explicit constant
  have hlip : LipschitzWith (Real.toNNReal (massActionLipschitzConstant N κ B))
      (N.massActionJacobianCLM κ x) := by
    refine LipschitzWith.of_dist_le_mul ?_
    intro u v
    rw [dist_eq_norm]
    have h := massActionJacobianCLM_norm_le N κ B x (u - v) hx
    rw [map_sub] at h
    rw [Real.coe_toNNReal (massActionLipschitzConstant N κ B) hC]
    exact h
  have hnn : ‖N.massActionJacobianCLM κ x‖₊
      ≤ Real.toNNReal (massActionLipschitzConstant N κ B) :=
    ContinuousLinearMap.opNNNorm_le_of_lipschitz hlip
  rw [massActionVectorField_fderiv]
  exact hnn

/-- **The undelayed mass-action vector field is Lipschitz on every bounded ball, with an
explicit constant.**

The vector field `N.massActionVectorField κ` is polynomial and is Lipschitz on the ball of radius
`B` with the constant `K(B)` of `massActionLipschitzConstant`. This theorem does not establish a
Lipschitz estimate for the full delay equation's history-dependent right-hand side.

Reference: the local Lipschitz estimate for polynomial vector fields (Hale, *Ordinary
Differential Equations*, Wiley 1980, Ch. 1). -/
theorem massActionVectorField_lipschitzOnWith_closedBall (N : Network S) (κ : N.RateConstants)
    (B : ℝ) :
    LipschitzOnWith (Real.toNNReal (massActionLipschitzConstant N κ B))
      (N.massActionVectorField κ) (Metric.closedBall 0 B) := by
  refine N.massActionVectorField_lipschitzOnWith_of_fderiv_le κ (convex_closedBall 0 B) ?_
  intro x hx
  have hxb : ‖x‖ ≤ B := by
    rw [Metric.mem_closedBall, dist_zero_right] at hx
    exact hx
  exact massActionVectorField_nnnorm_fderiv_le N κ B x hxb

end Network

/-! ### Axiom audit (informational) -/
#print axioms CRNT.Network.sourceDegree
#print axioms CRNT.Network.massActionLipschitzConstant
#print axioms CRNT.Network.massActionLipschitzConstant_nonneg
#print axioms CRNT.Network.massActionVectorField_fderiv
#print axioms CRNT.Network.abs_massActionMonomialGrad_le
#print axioms CRNT.Network.sum_abs_massActionMonomialGrad_le
#print axioms CRNT.Network.massActionJacobianCLM_apply_sum_coordinate
#print axioms CRNT.Network.massActionJacobianConstant
#print axioms CRNT.Network.massActionJacobianConstant_nonneg
#print axioms CRNT.Network.massActionJacobianCLM_norm_le_aux
#print axioms CRNT.Network.massActionJacobianConstant_le
#print axioms CRNT.Network.massActionJacobianCLM_norm_le
#print axioms CRNT.Network.massActionVectorField_nnnorm_fderiv_le
#print axioms CRNT.Network.massActionVectorField_lipschitzOnWith_closedBall

end CRNT
