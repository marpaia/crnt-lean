import CRNT.Equilibria.ComplexBalanceLinearStability
import CRNT.Equilibria.ComplexBalanceStructure
import CRNT.Theorems.DeficiencyZero.Toric
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# The nilpotent-Jacobian criterion for complex-balanced equilibria

This module adds the field-map leaf **S20**: the *nilpotent-Jacobian criterion* of
Horn--Jackson (1972), "The theory of open chemical reaction networks".

## The classical route

For a mass-action network `N` with rate constants `κ` the vector field factorises
(`CRNT.Dynamics.MassActionAlgebra`) as

```text
ẋ = Y (A_κ Ψ x)
```

with `Y` the complex matrix, `A_κ` the *weighted adjacency (kinetic Laplacian) matrix* of the
reaction graph, and `Ψ` the monomial map.  At a **complex-balanced** equilibrium `x*` the
kinetic matrix annihilates the monomial vector, `A_κ Ψ x* = 0`, and the linearisation of the
mass-action field is governed by `A_κ`.  The Perron–Frobenius theory of the nonnegative
matrix `A_κ` says that a nilpotent nonnegative matrix is the zero matrix: the spectral
radius of `A_κ` is an eigenvalue, so nilpotency forces every reaction rate to vanish.

The Lean route taken here is the *entropy-metric* form of the same argument, and it uses the
sum-of-squares identity already available in the repository
(`CRNT.Network.complexBalanceJacobianQuadratic_eq_neg_sum_sq`): at a positive complex-balanced
equilibrium the entropy-Hessian pairing of the mass-action Jacobian is a nonpositive sum of
squares,

```text
⟨h, J h⟩_{D(x*)⁻¹} = -(1/2) Σ_r q_r ⟨ν_r, D(x*)⁻¹ h⟩²  ≤ 0,
```

with `q_r = κ_r (x*)^{y_r} ≥ 0` the equilibrium one-way flux of reaction `r` and `ν_r` its
reaction vector.  A nilpotent matrix whose quadratic form is everywhere nonpositive must
vanish (`eq_zero_of_isNilpotent_of_weightedQuadraticForm_nonpos`): the trace of a nilpotent
matrix and of its square vanish, and these two facts kill the diagonal and the off-diagonal
entries.  Hence:

* the mass-action Jacobian at a positive complex-balanced equilibrium with nilpotent
  Jacobian vanishes identically (`nilpotent_jacobian_eq_zero_of_complexBalanced`);
* every reaction with positive flux at that equilibrium is stoichiometrically null, i.e. its
  source and target complexes coincide (`reactionVector_eq_zero_of_nilpotent_jacobian`);
* consequently the mass-action field of the network vanishes identically and *every*
  concentration is complex-balanced (`massActionVectorField_eq_zero_of_nilpotent_jacobian`,
  `isComplexBalanced_of_nilpotent_jacobian`).

This is the exact content of the Perron–Frobenius step of the classical criterion: the
nilpotent-Jacobian hypothesis at a positive complex-balanced equilibrium is possible only for
a *trivial* network, one whose reactions are all self-loops.  In particular

* a network all of whose reactions have nonzero net stoichiometry never has a nilpotent
  Jacobian at a positive complex-balanced equilibrium
  (`not_isNilpotentJacobian_of_complexBalanced_of_no_null_reaction`);
* the complex-balanced equilibrium is nevertheless unique in its positive compatibility
  class (`unique_complexBalanced_of_nilpotent_jacobian`), because the criterion makes the
  stoichiometric subspace trivial, so each compatibility class is a single point, and every
  positive compatibility class contains exactly one complex-balanced equilibrium
  (`exists_unique_isComplexBalanced_in_positiveClass_of_nilpotent_jacobian`).

## What is *not* proved here

The unrestricted form of the criterion — "a nilpotent Jacobian at `x*` makes `x*` the only
complex-balanced equilibrium" — is **false**, and this module proves it false: under the
nilpotency hypothesis every concentration of the network is complex-balanced, so the
complex-balanced equilibria are never unique.  A concrete witness is the self-loop network
`A → A` (`CRNT.Examples.NilpotentJacobian`): its Jacobian is the zero matrix, hence
nilpotent, and all of `ℝ` consists of complex-balanced equilibria.

Depends on: `CRNT.Equilibria.ComplexBalanceLinearStability`,
`CRNT.Theorems.DeficiencyZero.Toric`, Mathlib `LinearAlgebra.Matrix.Charpoly.Coeff`.
-/

namespace CRNT

namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ## Nilpotency of the mass-action Jacobian -/

/-- The mass-action Jacobian at `x` is **nilpotent**: some power of the Jacobian matrix is
the zero matrix.  This is the hypothesis of the Horn--Jackson nilpotent-Jacobian criterion. -/
def IsNilpotentJacobian (N : Network S) (κ : N.RateConstants) (x : Concentration S) : Prop :=
  IsNilpotent (N.massActionJacobian κ x)

/-! ## The linear-algebra core -/

section WeightedQuadraticForm

variable {n : Type} [Fintype n] [DecidableEq n]

/-- The `i`-th coordinate vector of `n → ℝ`. -/
def coordVec (i : n) : n → ℝ := fun j => if j = i then 1 else 0

omit [Fintype n] in
@[simp] theorem coordVec_self (i : n) : coordVec i i = 1 := by
  simp [coordVec]

omit [Fintype n] in
@[simp] theorem coordVec_ne (i j : n) (h : j ≠ i) : coordVec i j = 0 := by
  simp [coordVec, h]

/-- The quadratic form of a matrix `A` measured in the metric with weight `w`:
`∑ s, (h s / w s) * (A h) s`.  For `w` a positive concentration this is the Horn--Jackson
entropy-Hessian pairing `⟨h, A h⟩_{D(w)⁻¹}`. -/
noncomputable def weightedQuadraticForm (A : Matrix n n ℝ) (w : n → ℝ) (h : n → ℝ) : ℝ :=
  ∑ s, (h s / w s) * (A.mulVec h) s

/-- The action of a matrix on a coordinate vector. -/
theorem mulVec_coordVec (A : Matrix n n ℝ) (i j : n) :
    (A.mulVec (coordVec j)) i = A i j := by
  classical
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single j]
  · rw [coordVec_self, mul_one]
  · intro x _ hx
    rw [coordVec_ne j x hx, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- A weighted sum against a coordinate vector picks out the `i`-th coordinate. -/
theorem sum_coordVec (w : n → ℝ) (i : n) (g : n → ℝ) :
    (∑ s, (coordVec i s / w s) * g s) = g i / w i := by
  classical
  rw [Finset.sum_eq_single i]
  · rw [coordVec_self, one_div, div_eq_mul_inv, mul_comm]
  · intro s _ hs
    rw [coordVec_ne i s hs, zero_div, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- The weighted quadratic form of `A` on a coordinate vector. -/
theorem weightedQuadraticForm_coordVec (A : Matrix n n ℝ) (w : n → ℝ) (i : n) :
    weightedQuadraticForm A w (coordVec i) = A i i / w i := by
  unfold weightedQuadraticForm
  rw [sum_coordVec]
  rw [mulVec_coordVec]

/-- The weighted quadratic form of `A` on `e_i + t e_j`. -/
theorem weightedQuadraticForm_coordVec_add (A : Matrix n n ℝ) (w : n → ℝ) (i j : n) (t : ℝ) :
    weightedQuadraticForm A w (coordVec i + t • coordVec j)
      = A i i / w i + t * (A i j / w i + A j i / w j) + t ^ 2 * A j j / w j := by
  classical
  unfold weightedQuadraticForm
  have hmul : ∀ s, (A.mulVec (coordVec i + t • coordVec j)) s
      = (A.mulVec (coordVec i)) s + t * (A.mulVec (coordVec j)) s := by
    intro s
    rw [Matrix.mulVec_add, Matrix.mulVec_smul]
    rfl
  have harg : ∀ s, ((coordVec i + t • coordVec j) s) / w s
      = (coordVec i s) / w s + t * ((coordVec j s) / w s) := by
    intro s
    rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_div, mul_div_assoc]
  simp_rw [harg, hmul]
  have hprod : ∀ s,
      ((coordVec i s) / w s + t * ((coordVec j s) / w s)) *
          ((A.mulVec (coordVec i)) s + t * (A.mulVec (coordVec j)) s)
      = ((coordVec i s) / w s) * ((A.mulVec (coordVec i)) s)
          + t * (((coordVec i s) / w s) * ((A.mulVec (coordVec j)) s)
            + ((coordVec j s) / w s) * ((A.mulVec (coordVec i)) s))
          + t ^ 2 * (((coordVec j s) / w s) * ((A.mulVec (coordVec j)) s)) := by
    intro s
    ring
  rw [Finset.sum_congr rfl fun s _ => hprod s]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  rw [Finset.sum_add_distrib]
  rw [mul_add]
  rw [sum_coordVec, sum_coordVec, sum_coordVec, sum_coordVec]
  rw [mulVec_coordVec, mulVec_coordVec, mulVec_coordVec, mulVec_coordVec]
  ring

/-- The trace of a nilpotent matrix vanishes. -/
theorem trace_eq_zero_of_isNilpotent {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : IsNilpotent A) : Matrix.trace A = 0 :=
  (Matrix.isNilpotent_trace_of_isNilpotent hA).eq_zero

/-- **Nilpotency plus a nonpositive weighted quadratic form forces the matrix to vanish.**

This is the linear-algebra core of the nilpotent-Jacobian criterion, the Perron--Frobenius
step in its matrix form.  A matrix whose weighted quadratic form `∑ s, (h s / w s) * (A h) s`
is everywhere nonpositive has a nonpositive diagonal; nilpotency makes the trace (and the
trace of the square) vanish, and the two facts together kill every entry. -/
theorem eq_zero_of_isNilpotent_of_weightedQuadraticForm_nonpos
    (A : Matrix n n ℝ) (w : n → ℝ) (hw : ∀ s, 0 < w s)
    (hnil : IsNilpotent A)
    (hq : ∀ h : n → ℝ, weightedQuadraticForm A w h ≤ 0) : A = 0 := by
  classical
  -- (1) the diagonal entries are nonpositive
  have hdiag : ∀ i, A i i ≤ 0 := by
    intro i
    have h := hq (coordVec i)
    rw [weightedQuadraticForm_coordVec] at h
    have hwi : 0 < w i := hw i
    have h' : A i i ≤ 0 * w i := (div_le_iff₀ hwi).mp h
    linarith
  -- (2) the trace vanishes, hence so does every diagonal entry
  have htrace : Matrix.trace A = 0 := trace_eq_zero_of_isNilpotent A hnil
  have htrace' : (∑ i, A i i) = 0 := by
    simpa [Matrix.trace, Matrix.diag_apply] using htrace
  have hdiag0 : ∀ i, A i i = 0 := by
    intro i
    have hnn : ∀ j ∈ (Finset.univ : Finset n), 0 ≤ -A j j :=
      fun j _ => neg_nonneg.mpr (hdiag j)
    have hsumneg : (∑ j, -A j j) = 0 := by
      rw [Finset.sum_neg_distrib, htrace']
      simp
    have h := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsumneg
    have hz := h i (Finset.mem_univ i)
    linarith
  -- (3) the weighted "skew" relation between the off-diagonal entries
  have hgen : ∀ (i j : n) (t : ℝ), t * (A i j / w i + A j i / w j) ≤ 0 := by
    intro i j t
    have h := hq (coordVec i + t • coordVec j)
    rw [weightedQuadraticForm_coordVec_add] at h
    have hii : A i i = 0 := hdiag0 i
    have hjj : A j j = 0 := hdiag0 j
    simp only [hii, hjj, zero_div, mul_zero, add_zero] at h
    linarith
  have hskew : ∀ i j, A i j / w i + A j i / w j = 0 := by
    intro i j
    have h1 := hgen i j 1
    have h2 := hgen i j (-1)
    linarith
  -- (4) the trace of the square vanishes and kills the off-diagonal entries
  have hsquare : IsNilpotent (A * A) := by
    rcases hnil with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have hpow : ∀ m, (A * A) ^ m = A ^ (m * 2) := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [pow_succ, ih, ← Matrix.mul_assoc, ← pow_succ, ← pow_succ]
        congr 1
        ring
    rw [hpow, pow_mul, pow_two, hk, zero_mul]
  have htrace2 : Matrix.trace (A * A) = 0 := trace_eq_zero_of_isNilpotent (A * A) hsquare
  have hsum : (∑ i, ∑ k, A i k * A k i) = 0 := by
    have h2 : Matrix.trace (A * A) = ∑ i, ∑ k, A i k * A k i := by
      simp [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    rw [h2] at htrace2
    exact htrace2
  have hkey : ∀ i k, A i k * A k i = -((A i k) ^ 2 * (w k) / (w i)) := by
    intro i k
    have h := hskew i k
    have hwi : w i ≠ 0 := (hw i).ne'
    have hwk : w k ≠ 0 := (hw k).ne'
    have hmul : A i k * w k + w i * A k i = 0 := by
      field_simp [hwi, hwk] at h
      simpa using h
    have hmul2 : w i * A k i = -(A i k * w k) := by linarith
    have hcore : A i k * A k i * w i = -(A i k)^2 * (w k) := by
      calc A i k * A k i * w i = A i k * (w i * A k i) := by ring
        _ = A i k * (-(A i k * w k)) := by rw [hmul2]
        _ = -(A i k)^2 * (w k) := by ring
    have h2 : A i k * A k i = (-(A i k)^2 * (w k)) / (w i) := (eq_div_iff hwi).mpr hcore
    rw [h2]
    field_simp [hwi]
  have hsum' : (∑ i, ∑ k, (A i k) ^ 2 * (w k) / (w i)) = 0 := by
    have hneg : (∑ i, ∑ k, A i k * A k i)
        = -∑ i, ∑ k, (A i k) ^ 2 * (w k) / (w i) := by
      calc (∑ i, ∑ k, A i k * A k i)
          = ∑ i, ∑ k, -((A i k) ^ 2 * (w k) / (w i)) := by
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro k _
            exact hkey i k
        _ = -∑ i, ∑ k, (A i k) ^ 2 * (w k) / (w i) := by
          have h1 : (∑ i, ∑ k, -((A i k) ^ 2 * (w k) / (w i)))
              = ∑ i, -∑ k, (A i k) ^ 2 * (w k) / (w i) := by
            apply Finset.sum_congr rfl
            intro i _
            exact Finset.sum_neg_distrib (f := fun k => (A i k) ^ 2 * (w k) / (w i))
          rw [h1, Finset.sum_neg_distrib]
    rw [hneg] at hsum
    linarith
  have houter : ∀ i, (∑ k, (A i k) ^ 2 * (w k) / (w i)) = 0 := by
    have hnn : ∀ j ∈ (Finset.univ : Finset n),
        0 ≤ ∑ k, (A j k) ^ 2 * (w k) / (w j) := by
      intro j _
      have hwj : 0 < w j := hw j
      exact Finset.sum_nonneg fun k _ => by
        have hwk : 0 < w k := hw k
        positivity
    have h := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum'
    intro i
    exact h i (Finset.mem_univ i)
  have hzero : ∀ i k, (A i k) ^ 2 * (w k) / (w i) = 0 := by
    intro i k
    have hwi : 0 < w i := hw i
    have hwk : 0 < w k := hw k
    have hnn : ∀ j ∈ (Finset.univ : Finset n), 0 ≤ (A i j) ^ 2 * (w j) / (w i) := by
      intro j _
      have hwj : 0 < w j := hw j
      positivity
    have h := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp (houter i)
    exact h k (Finset.mem_univ k)
  have hentry : ∀ i k, A i k = 0 := by
    intro i k
    have hwi : w i ≠ 0 := (hw i).ne'
    have hwk : w k ≠ 0 := (hw k).ne'
    have hsq : (A i k) ^ 2 = 0 := by
      have h := div_eq_zero_iff.mp (hzero i k)
      rcases h with h1 | h2
      · rcases mul_eq_zero.mp h1 with h1 | h1
        · exact h1
        · exact absurd h1 hwk
      · exact absurd h2 hwi
    exact sq_eq_zero_iff.mp hsq
  funext i k
  exact hentry i k

end WeightedQuadraticForm

/-! ## The criterion -/

/-- The entropy-metric quadratic form of the mass-action Jacobian is the weighted quadratic
form of the Jacobian matrix with weight the equilibrium concentration. -/
theorem complexBalanceJacobianQuadratic_eq_weightedQuadraticForm
    (N : Network S) (κ : N.RateConstants) (xstar h : Concentration S) :
    N.complexBalanceJacobianQuadratic κ xstar h
      = weightedQuadraticForm (N.massActionJacobian κ xstar) xstar h := by
  rfl

/-- **The nilpotent-Jacobian criterion, first step.**  At a positive complex-balanced
equilibrium the mass-action Jacobian has a nonpositive entropy-metric quadratic form; if the
Jacobian is nilpotent, it vanishes identically.

This is the Perron–Frobenius step of the classical criterion in the entropy metric: a
nilpotent matrix with a nonpositive quadratic form is the zero matrix. -/
theorem nilpotent_jacobian_eq_zero_of_complexBalanced
    (N : Network S) (κ : N.RateConstants) {xstar : Concentration S}
    (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    (hnil : IsNilpotentJacobian N κ xstar) :
    N.massActionJacobian κ xstar = 0 := by
  refine eq_zero_of_isNilpotent_of_weightedQuadraticForm_nonpos
    (N.massActionJacobian κ xstar) xstar hxs hnil ?_
  intro h
  rw [← complexBalanceJacobianQuadratic_eq_weightedQuadraticForm]
  exact N.complexBalanceJacobianQuadratic_nonpos κ hxs hcb h

/-- **The nilpotent-Jacobian criterion, second step.**  At a positive complex-balanced
equilibrium with nilpotent Jacobian, every reaction that carries a positive flux has zero net
stoichiometry: its source and target complexes coincide.

The proof is the sum-of-squares identity of the Horn--Jackson entropy: the vanishing
quadratic form forces the logarithmic linear form of every active reaction to vanish
identically, and that is exactly the vanishing of the reaction vector. -/
theorem reactionVector_eq_zero_of_nilpotent_jacobian
    (N : Network S) (κ : N.RateConstants) {xstar : Concentration S}
    (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    (hnil : IsNilpotentJacobian N κ xstar)
    (r : N.R) (hflux : 0 < N.equilibriumReactionFlux κ xstar r) :
    N.reactionVector r = 0 := by
  have hJ : N.massActionJacobian κ xstar = 0 :=
    N.nilpotent_jacobian_eq_zero_of_complexBalanced κ hxs hcb hnil
  -- the entropy-metric quadratic form vanishes identically
  have hquad : ∀ h : Concentration S, N.complexBalanceJacobianQuadratic κ xstar h = 0 := by
    intro h
    have hmul : (N.massActionJacobian κ xstar).mulVec h = 0 := by
      rw [hJ]
      exact Matrix.zero_mulVec h
    unfold complexBalanceJacobianQuadratic entropyHessianPairing
    rw [hmul]
    simp
  -- the logarithmic linear form of `r` vanishes identically
  have hlin : ∀ h : Concentration S, N.reactionLogLinearForm xstar h r = 0 := by
    intro h
    have hsq := N.complexBalanceJacobianQuadratic_eq_neg_sum_sq κ hxs hcb h
    have hq0 := hquad h
    rw [hsq] at hq0
    have hsum : (∑ r' : N.R, N.equilibriumReactionFlux κ xstar r' *
        (N.reactionLogLinearForm xstar h r') ^ 2) = 0 := by linarith
    have hnn : ∀ r' ∈ (Finset.univ : Finset N.R),
        0 ≤ N.equilibriumReactionFlux κ xstar r' *
          (N.reactionLogLinearForm xstar h r') ^ 2 := by
      intro r' _
      exact mul_nonneg (N.massActionRate_pos κ r' hxs).le (sq_nonneg _)
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum
    have hz := hterm r (Finset.mem_univ r)
    have hsq0 : (N.reactionLogLinearForm xstar h r) ^ 2 = 0 :=
      (mul_eq_zero.mp hz).resolve_left hflux.ne'
    exact sq_eq_zero_iff.mp hsq0
  -- evaluate at a coordinate vector
  funext s
  have h := hlin (coordVec s)
  have hform : N.reactionLogLinearForm xstar (coordVec s) r
      = N.reactionVector r s / xstar s := by
    unfold reactionLogLinearForm
    rw [Finset.sum_eq_single s]
    · rw [coordVec_self, one_div, div_eq_mul_inv]
    · intro s' _ hs'
      rw [coordVec_ne s s' hs', zero_div, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ s) h
  rw [hform] at h
  rcases div_eq_zero_iff.mp h with h1 | h2
  · exact h1
  · exact absurd h2 (hxs s).ne'

/-- **The nilpotent-Jacobian criterion, third step.**  At a positive complex-balanced
equilibrium with nilpotent Jacobian every reaction is stoichiometrically null, so the
mass-action field of the network vanishes identically. -/
theorem reactionVector_eq_zero_of_nilpotent_jacobian_of_all
    (N : Network S) (κ : N.RateConstants) {xstar : Concentration S}
    (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    (hnil : IsNilpotentJacobian N κ xstar)
    (r : N.R) : N.reactionVector r = 0 := by
  have hflux : 0 < N.equilibriumReactionFlux κ xstar r :=
    N.massActionRate_pos κ r hxs
  exact N.reactionVector_eq_zero_of_nilpotent_jacobian κ hxs hcb hnil r hflux

/-- **The nilpotent-Jacobian criterion, third step (continued).**  At a positive
complex-balanced equilibrium with nilpotent Jacobian the mass-action field of the network
vanishes identically: the network is dynamically trivial. -/
theorem massActionVectorField_eq_zero_of_nilpotent_jacobian
    (N : Network S) (κ : N.RateConstants) {xstar : Concentration S}
    (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    (hnil : IsNilpotentJacobian N κ xstar)
    (x : Concentration S) : N.massActionVectorField κ x = 0 := by
  funext s
  unfold Network.massActionVectorField
  refine Finset.sum_eq_zero fun r _ => ?_
  have hnull : N.reactionVector r = 0 :=
    N.reactionVector_eq_zero_of_nilpotent_jacobian_of_all κ hxs hcb hnil r
  have hzero : ∀ t, N.reactionVector r t = 0 := fun t => congrFun hnull t
  simp only [hzero, mul_zero]

/-- **The nilpotent-Jacobian criterion, third step (continued).**  At a positive
complex-balanced equilibrium with nilpotent Jacobian *every* concentration of the network is
complex balanced: the complex-balanced equilibria are all of `ℝ^S`.  This is why the
unrestricted form of the criterion ("a nilpotent Jacobian makes the complex-balanced
equilibrium unique") cannot hold. -/
theorem isComplexBalanced_of_nilpotent_jacobian
    (N : Network S) (κ : N.RateConstants) {xstar : Concentration S}
    (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    (hnil : IsNilpotentJacobian N κ xstar)
    (x : Concentration S) : N.IsComplexBalanced κ x := by
  have hnull : ∀ r : N.R, N.reactionVector r = 0 :=
    fun r => N.reactionVector_eq_zero_of_nilpotent_jacobian_of_all κ hxs hcb hnil r
  have hsrc : ∀ r : N.R, (N.reaction r).source = (N.reaction r).target := by
    intro r
    funext s
    have h := congrFun (hnull r) s
    simp only [Network.reactionVector_apply] at h
    have h' : (N.reaction r).source s = (N.reaction r).target s := by
      have h'' : ((N.reaction r).target s : ℝ) = ((N.reaction r).source s : ℝ) :=
        sub_eq_zero.mp h
      exact_mod_cast h''.symm
    exact h'
  intro c hc
  -- the inflow and the outflow of `c` agree because every reaction is a self-loop
  have hkey : ∀ r : N.R,
      (if (N.reaction r).target = c then N.massActionRate κ r x else 0)
        = (if (N.reaction r).source = c then N.massActionRate κ r x else 0) := by
    intro r
    rw [hsrc r]
  unfold Network.inflow Network.outflow
  rw [Finset.sum_congr rfl fun r _ => hkey r]

/-- **No-go form of the nilpotent-Jacobian criterion.**  A network all of whose reactions
have nonzero net stoichiometry never has a nilpotent Jacobian at a positive complex-balanced
equilibrium.  This is the Perron–Frobenius content of the classical criterion: nilpotency
of the Jacobian forces the weighted adjacency matrix to vanish, hence forces every reaction
to be stoichiometrically null. -/
theorem not_isNilpotentJacobian_of_complexBalanced_of_no_null_reaction
    (N : Network S) (κ : N.RateConstants) {xstar : Concentration S}
    (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    (hr : ∃ r : N.R, N.reactionVector r ≠ 0) :
    ¬ IsNilpotentJacobian N κ xstar := by
  intro hnil
  have hnull := N.reactionVector_eq_zero_of_nilpotent_jacobian_of_all κ hxs hcb hnil
  obtain ⟨r, hrv⟩ := hr
  exact hrv (hnull r)

/-- **Uniqueness of the complex-balanced equilibrium (the nilpotent-Jacobian criterion).**

Let `x*` be a positive complex-balanced equilibrium whose mass-action Jacobian is nilpotent.
Then `x*` is the unique complex-balanced equilibrium of `N` in its positive stoichiometric
compatibility class.

The proof is the criterion itself: the nilpotent Jacobian forces every reaction to be
stoichiometrically null, so the stoichiometric subspace is trivial and each compatibility
class is a single point.  (The uniqueness of the complex-balanced equilibrium in a positive
compatibility class is, independently, the classical Horn--Jackson uniqueness theorem, which
the repository already proves in `CRNT.Network.isComplexBalanced_unique_in_positiveClass`.) -/
theorem unique_complexBalanced_of_nilpotent_jacobian
    (N : Network S) (κ : N.RateConstants) (xstar : Concentration S)
    (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    (hnil : IsNilpotentJacobian N κ xstar) :
    ∀ y : Concentration S, y ∈ N.positiveCompatibilityClass xstar →
      N.IsComplexBalanced κ y → y = xstar := by
  intro y hy _
  -- the nilpotent-Jacobian criterion forces every reaction to be stoichiometrically null,
  -- so the stoichiometric subspace is trivial and the compatibility class is a single point
  have hnull : ∀ r : N.R, N.reactionVector r = 0 :=
    N.reactionVector_eq_zero_of_nilpotent_jacobian_of_all κ hxs hcb hnil
  have hspan : N.stoichSubspace = ⊥ := by
    refine le_antisymm ?_ bot_le
    refine Submodule.span_le.2 ?_
    rintro v ⟨r, rfl⟩
    simp [hnull r]
  obtain ⟨hcompat, _⟩ := hy
  have hmem : y - xstar ∈ N.stoichSubspace := hcompat
  rw [hspan] at hmem
  have hyz : y - xstar = 0 := hmem
  exact sub_eq_zero.mp hyz

/-- **The unrestricted form of the criterion.**  If in addition the network has no
stoichiometrically null reaction, then `x*` is the only *positive* complex-balanced
equilibrium of `N` — and the nilpotent-Jacobian hypothesis is then contradictory, by
`not_isNilpotentJacobian_of_complexBalanced_of_no_null_reaction`.  The theorem is kept
because it is the exact shape of the classical statement; it is proved, but it is proved from
a contradictory pair of hypotheses. -/
theorem unique_complexBalanced_of_nilpotent_jacobian_of_no_null_reaction
    (N : Network S) (κ : N.RateConstants) (xstar : Concentration S)
    (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    (hnil : IsNilpotentJacobian N κ xstar)
    (hr : ∃ r : N.R, N.reactionVector r ≠ 0) :
    ∀ y : Concentration S, y.Positive → N.IsComplexBalanced κ y → y = xstar := by
  have hcontra : False :=
    N.not_isNilpotentJacobian_of_complexBalanced_of_no_null_reaction κ hxs hcb hr hnil
  exact hcontra.elim

/-- **One complex-balanced equilibrium per positive compatibility class.**  Under the
nilpotent-Jacobian hypothesis, every positive compatibility class of `N` contains exactly one
complex-balanced equilibrium.  Existence is the toric inclusion
(`CRNT.Network.exists_isComplexBalanced_in_positiveClass`); uniqueness follows from the
criterion, which makes the stoichiometric subspace trivial, so each positive compatibility
class is a single point. -/
theorem exists_unique_isComplexBalanced_in_positiveClass_of_nilpotent_jacobian
    (N : Network S) (κ : N.RateConstants) (xstar : Concentration S)
    (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    (hnil : IsNilpotentJacobian N κ xstar) :
    ∀ x₀ : Concentration S, x₀.Positive →
      ∃! y : Concentration S, y ∈ N.positiveCompatibilityClass x₀ ∧ N.IsComplexBalanced κ y := by
  intro x₀ hx₀
  obtain ⟨y, hy, hcb_y⟩ := N.exists_isComplexBalanced_in_positiveClass κ hxs hcb hx₀
  refine ⟨y, ⟨hy, hcb_y⟩, ?_⟩
  intro z hz
  obtain ⟨hzc, _⟩ := hz
  obtain ⟨hzc', _⟩ := hzc
  -- the nilpotent-Jacobian criterion makes the stoichiometric subspace trivial, so each
  -- positive compatibility class is a single point and contains one complex-balanced equilibrium
  have hnull : ∀ r : N.R, N.reactionVector r = 0 :=
    N.reactionVector_eq_zero_of_nilpotent_jacobian_of_all κ hxs hcb hnil
  have hspan : N.stoichSubspace = ⊥ := by
    refine le_antisymm ?_ bot_le
    refine Submodule.span_le.2 ?_
    rintro v ⟨r, rfl⟩
    simp [hnull r]
  have hzmem : z - x₀ ∈ N.stoichSubspace := hzc'
  rw [hspan] at hzmem
  have hzy : z = x₀ := sub_eq_zero.mp hzmem
  have hymem : y - x₀ ∈ N.stoichSubspace := hy.1
  rw [hspan] at hymem
  have hyx : y = x₀ := sub_eq_zero.mp hymem
  exact hzy.trans hyx.symm

end Network

end CRNT

/-! ## A concrete instance

The nilpotent-Jacobian criterion is *sharp*: the nilpotent case is exactly the trivial one.
The self-loop network `A → A` has a nilpotent mass-action Jacobian at every concentration
(the Jacobian is the zero matrix), and every concentration of `ℝ` is a complex-balanced
equilibrium — so the nilpotent-Jacobian hypothesis does not single out one equilibrium.
The uniqueness conclusion of the criterion therefore has to be read with the class
constraint, or with the hypothesis that the network has no stoichiometrically null reaction
(see `CRNT.Network.unique_complexBalanced_of_nilpotent_jacobian` and
`CRNT.Network.not_isNilpotentJacobian_of_complexBalanced_of_no_null_reaction`). -/

namespace CRNT.Examples.NilpotentJacobian

open CRNT

/-- One species, `A`. -/
abbrev Species := Fin 1

/-- One reaction channel. -/
abbrev Rxn := Fin 1

/-- The complex `A`. -/
def cA : Complex Species := fun _ => 1

/-- The single reaction channel. -/
def r0 : Rxn := ⟨0, by norm_num⟩

/-- The reaction map: the self-reaction `A → A`. -/
def rxn : Rxn → Reaction Species := fun _ => { source := cA, target := cA }

/-- The network `A → A`. -/
def N : Network Species :=
  { R := Rxn, decEqR := inferInstance, fintypeR := inferInstance, reaction := rxn }

/-- Rate constants: a single strictly positive rate. -/
def rates (k : ℝ) (hk : 0 < k) : Network.RateConstants N where
  k := fun _ => k
  positive := by intro r; exact hk

/-- The reaction vector of the self-reaction vanishes. -/
theorem reactionVector_zero : N.reactionVector r0 = 0 := by
  funext s
  simp [Network.reactionVector, N, rxn, Reaction.vector, cA]

/-- The only complex of the network is `A`. -/
theorem complexes_eq : N.complexes = {cA} := by decide

/-- The mass-action field of the self-loop network vanishes identically. -/
theorem massActionVectorField_eq_zero (k : ℝ) (hk : 0 < k) (x : Concentration Species) :
    N.massActionVectorField (rates k hk) x = 0 := by
  funext s
  simp [Network.massActionVectorField, Network.reactionVector, N, rxn, Reaction.vector, cA]

/-- The mass-action Jacobian of the self-loop network vanishes identically. -/
theorem massActionJacobian_eq_zero (k : ℝ) (hk : 0 < k) (x : Concentration Species) :
    N.massActionJacobian (rates k hk) x = 0 := by
  funext i j
  simp [Network.massActionJacobian, Network.reactionVector, N, rxn, Reaction.vector, cA,
    massActionMonomialGrad]

/-- **The Jacobian of the self-loop network is nilpotent at every concentration.** -/
theorem isNilpotentJacobian (k : ℝ) (hk : 0 < k) (x : Concentration Species) :
    Network.IsNilpotentJacobian N (rates k hk) x := by
  refine ⟨1, ?_⟩
  rw [massActionJacobian_eq_zero]
  simp

/-- Every concentration is complex balanced for the self-loop network: the single reaction
is a self-loop, so inflow and outflow agree at the only complex. -/
theorem isComplexBalanced (k : ℝ) (hk : 0 < k) (x : Concentration Species) :
    N.IsComplexBalanced (rates k hk) x := by
  intro c hc
  rw [complexes_eq] at hc
  simp only [Finset.mem_singleton] at hc
  rcases hc with rfl | rfl
  simp [Network.inflow, Network.outflow, N, rxn, cA, Network.massActionRate,
    Complex.massActionMonomial]

/-- The concentration `x* = 1` is a positive complex-balanced equilibrium of the
self-loop network. -/
theorem equilibrium_isComplexBalanced (k : ℝ) (hk : 0 < k) :
    N.IsComplexBalanced (rates k hk) (fun _ => 1) := isComplexBalanced k hk _

/-- **The nilpotent-Jacobian criterion at work.**  At the positive complex-balanced
equilibrium `x* = 1` the mass-action Jacobian is nilpotent, so the criterion
(`CRNT.Network.nilpotent_jacobian_eq_zero_of_complexBalanced`) makes it vanish. -/
theorem equilibrium_jacobian_eq_zero (k : ℝ) (hk : 0 < k) :
    N.massActionJacobian (rates k hk) (fun _ => 1) = 0 := by
  exact N.nilpotent_jacobian_eq_zero_of_complexBalanced (rates k hk) (by intro s; simp)
    (equilibrium_isComplexBalanced k hk) (isNilpotentJacobian k hk _)

/-- **The nilpotent case does not single out one equilibrium.**  Two distinct
concentrations of the self-loop network are complex-balanced equilibria, so the
nilpotent-Jacobian hypothesis alone cannot give uniqueness of the complex-balanced
equilibrium: the criterion forces the network to be trivial, and a trivial network has all
of `ℝ` as its set of complex-balanced equilibria. -/
theorem two_distinct_complexBalanced (k : ℝ) (hk : 0 < k) :
    N.IsComplexBalanced (rates k hk) (fun _ => 1) ∧
      N.IsComplexBalanced (rates k hk) (fun _ => 2) :=
  ⟨isComplexBalanced k hk _, isComplexBalanced k hk _⟩

end CRNT.Examples.NilpotentJacobian
