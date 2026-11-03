import CRNT.Multistationarity.MultistationarityRegionDescription
import CRNT.LinearAlgebra.CauchyBinet
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Finprod

/-!
# The Cauchy–Binet expansion of the reduced determinant: the circuit reading in higher rank

This module supplies the part of field-map leaf **M13** ("Parameter regions for
multistationarity") that was still missing after
`CRNT.Multistationarity.MultistationarityRegionDescription`: the **higher-rank circuit reading**
of the reduced determinant.

## What was known

`CRNT.Multistationarity.MultistationarityRegionDescription` gave the *rank-one* circuit reading
of the multistationarity region:

* the reduced determinant of a rank-one network is the **difference of the two directional
  fluxes** of the circuit (`CRNT.Network.reducedDerivOf_eq_forward_sub_backward`);
* the circuits of a rank-one network are **pairs** of oppositely oriented reactions
  (`CRNT.Network.rankOne_circuit_is_pair`), and the region condition is the **comparison of two
  products** of a rate constant with a monomial-derivative factor
  (`CRNT.Network.reducedDerivOf_pos_iff_two_reaction_circuit`);
* the proposed *single-product* reading is **refuted by proof**: the rank-one reduced determinant
  is an **affine** functional of the rate constants, whereas a product is multilinear
  (`CRNT.Network.not_eq_rateProduct_mul`).

The notes of leaf M13 record exactly what was missing:

> **Still missing: the higher-rank circuit reading** — the reduced determinant in rank `s ≥ 2` is a
> genuine Cauchy–Binet sum over circuits of the chart, and the sign rule there is different.

This module delivers it.

## 1. The general Cauchy–Binet formula for a sum of matrices

The reduced Jacobian of a network of stoichiometric rank `s` is a **sum of matrices**, one per
reaction:

```
M = ∑_r κ_r A_r
```

where `A_r` is the *chart matrix* of the reaction `r`.  The determinant of such a sum is
multilinear, and the classical Cauchy–Binet formula expands it:

* `Matrix.det_sum_eq_sum_tuples` — the **`n`-tuple form**: the determinant of `∑_r κ_r A_r` is the
  sum over the `n`-tuples `f : Fin n → ι` of the product `∏_j κ_{f j}` times the determinant of
  the matrix whose `(p, i)`-entry is `A_{f i} p i`.  This is proved directly from the Leibniz
  formula and is valid over any commutative ring.
* `Matrix.det_mul_diag_mul_eq_sum_subsets` — the **subset form** (the classical Cauchy–Binet
  formula): for `M = U * (diag κ * W)` the determinant is the sum over the `m`-element subsets
  `S` of the index set of `det (U restricted to S) * (∏_{r ∈ S} κ r) * det (W restricted to S)`.

The subset form is the one that carries the **circuit reading**: every term is a **product of `s`
rate constants** — one per reaction of the supporting subset — times a determinant.

## 2. The chart matrices of a network

Fix a chart of the stoichiometric subspace, i.e. a pair

* `chart : (Fin s → ℝ) →L[ℝ] (S → ℝ)` — the chart (the repository's own `Network.stoichChart` is
  the canonical instance), and
* `proj : (S → ℝ) →L[ℝ] (Fin s → ℝ)` — the dual projection (`Network.stoichProj`).

For a reaction `r` and a concentration `x` the two chart data are

* `Network.chartGradient` — the **chart gradient** `g_r j = ∑_k ∂_k (source monomial of r)(x) ·
  (chart e_j) k`: the directional derivative of the source monomial along the `j`-th chart
  direction;
* `Network.chartVector` — the **chart reaction vector** `v_r = proj (reactionVector r)`: the
  reaction vector, read in the chart coordinates.

The reduced Jacobian is then the rank-one sum

```
M i j = ∑_r κ_r · g_r j · v_r i
```

(`Network.reducedJacobianInChart_apply`), i.e. `M = V * (diag κ * G)` with `V` the matrix of the
chart reaction vectors and `G` the matrix of the chart gradients.

## 3. The Cauchy–Binet expansion of the reduced determinant

`Network.reducedJacobianInChart_det_eq_cauchyBinet` is the main statement: the determinant of the
reduced Jacobian is the sum, over the `s`-element subsets `S` of the reactions, of

* `Network.circuitMatrix` — the **circuit matrix** of `S`: the matrix whose **columns** are the
  chart reaction vectors of the reactions of `S` — its determinant vanishes exactly when those
  reaction vectors are linearly dependent, i.e. when `S` carries a circuit;
* the **product of the rate constants** `∏_{r ∈ S} κ_r`;
* `Network.gradientMatrix` — the **gradient matrix** of `S`: the matrix whose **rows** are the
  chart gradients of the reactions of `S`.

`Network.reducedJacobian_det_eq_cauchyBinet` is the same statement for the repository's own
canonical chart (`Network.stoichChart` and its dual `Network.stoichProj`), and
`Network.reducedJacobian_eq_reducedJacobianInChart` identifies the two.

## 4. The circuit reading

`Network.IsPositiveCircuit` is the reaction-network notion of a **circuit**: a set of reactions
whose reaction vectors admit a *positive* linear dependence.

* `Network.chartVector_positiveDep_of_circuit` — the chart vectors of a circuit are positively
  dependent (the dual projection is linear);
* `Network.circuitMatrix_det_eq_zero_of_dep` — **a Cauchy–Binet term vanishes as soon as the
  reaction vectors of its reactions are linearly dependent**;
* `Network.circuitMatrix_det_eq_zero_of_circuit` — **a Cauchy–Binet term vanishes as soon as
  its reactions contain a circuit**.

This is the precise sense in which the higher-rank reduced determinant is a *sum* over
configurations of `s` reactions, each contributing a **product of `s` rate constants** with the
sign of the two minors — in contrast to the rank-one case, where the reduced determinant is
*affine* in the rate constants (`CRNT.Network.not_eq_rateProduct_mul`) and the region condition
is a *comparison* of two products
(`CRNT.Network.reducedDerivOf_pos_iff_two_reaction_circuit`).

## 5. The product-of-rates structure

Every term of the Cauchy–Binet expansion of the reduced determinant in rank `s` is a **product of
`s` rate constants**, one factor per reaction of the supporting subset, multiplied by the two
minors (the circuit minor and the gradient minor).  The reduced determinant in rank `s ≥ 2` is
therefore a *multilinear* (degree `s`) object, in contrast to the rank-one reduced determinant,
which is an *affine* (indeed linear) function of the rate constants
(`CRNT.Network.reducedDerivOf_add`, `CRNT.Network.not_eq_rateProduct_mul`).

## 6. A rank-two instance

`Network.exU` and `Network.exG` are the chart reaction vectors and the chart gradients of a
rank-two network on the species `A`, `B`, `C` with the four reactions `A → B`, `B → A`,
`B → C`, `C → A`, in the chart with basis `A → B` and `B → C`; `Network.exκ` are
the rate constants `(2, 3, 5, 7)`.

* `Network.ex_det` — the reduced determinant of the instance is `80`;
* `Network.ex_cauchyBinet` — the Cauchy–Binet sum of the instance is `80` as well — the
  same value, term by term;
* `Network.ex_circuit_pair` — the pair `{A → B, B → A}` is a **circuit**: its two chart
  reaction vectors are opposite, the circuit matrix of the pair is singular, and the
  corresponding Cauchy–Binet term vanishes;
* `Network.ex_pair_02` and `Network.ex_pair_13` — the non-circuit pairs contribute the
  **product of their two rate constants**: `+2 · 5 = 10` and `+3 · 7 = 21`.

## 7. Relation to leaf M13

Leaf M13 asks for the *parameter regions* for multistationarity.  This module does not change the
description of the region — that is the rank-one statement
`CRNT.Network.rateMultistationarityRegion_iff_classIsMultistationary` — but it supplies the
**algebraic content of the reduced determinant** in every rank, which is the analytic quantity
whose sign decides the region:

* in rank one the reduced determinant is a **comparison** of two directional fluxes
  (`CRNT.Network.reducedDerivOf_eq_forward_sub_backward`), and the classical single-product sign
  rule is *refuted* (`CRNT.Network.not_eq_rateProduct_mul`);
* in rank `s ≥ 2` the reduced determinant is a **Cauchy–Binet sum of products of `s` rate
  constants** over the circuits of the chart.

Depends on: `CRNT.Multistationarity.MultistationarityRegionDescription`,
`CRNT.LinearAlgebra.CauchyBinet`.
-/

/-! ## 1. The general Cauchy–Binet formula for a sum of matrices -/

namespace Matrix

open Equiv Equiv.Perm Finset
open scoped BigOperators

variable {ι : Type*} [Fintype ι]
variable {m n : ℕ}
variable {R : Type*} [CommRing R]

local notation "ε " σ:arg => ((sign σ : ℤ) : R)

/-- **Applying a finite sum to a point.**  For a family of functions `g c : β → γ`, the sum of
the functions may be applied to a point, entry by entry. -/
theorem fintype_sum_apply {α : Type*} [Fintype α] {β : Type*} {M : β → Type*}
    [∀ b, AddCommMonoid (M b)] (b : β) (g : α → (b : β) → M b) :
    (∑ c, g c) b = ∑ c, g c b :=
  Finset.sum_apply b (Finset.univ : Finset α) g

/-- **Swapping two finite sums.**  The `Finset` version of the lemma is stated with the
double-binder notation; this is the `Fintype` version. -/
theorem fintype_sum_comm {α β : Type*} [Fintype α] [Fintype β] {S : Type*} [AddCommMonoid S]
    (f : α → β → S) : ∑ x, ∑ y, f x y = ∑ y, ∑ x, f x y := by
  have h := Finset.sum_comm (f := f) (β := S) (s := (Finset.univ : Finset α))
    (t := (Finset.univ : Finset β))
  simpa only [Finset.mem_univ, true_and, Finset.sum_const_zero, Finset.sum_ite_irrel] using h

/-- **Multiplying a finite sum.** -/
theorem fintype_mul_sum {α : Type*} [Fintype α] {S : Type*} [NonUnitalNonAssocSemiring S]
    (a : S) (f : α → S) : (∑ i, a * f i) = a * ∑ i, f i := by
  have h := Finset.mul_sum (s := (Finset.univ : Finset α)) (f := f) (a := a)
  simpa only [Finset.mem_univ, true_and] using h.symm

/-- **Splitting a finite product into two.** -/
theorem fintype_prod_mul_distrib {α : Type*} [Fintype α] {S : Type*} [CommSemiring S]
    (f g : α → S) : (∏ x, f x * g x) = (∏ x, f x) * ∏ x, g x := by
  have h := Finset.prod_mul_distrib (s := (Finset.univ : Finset α)) (f := f) (g := g)
  simpa only [Finset.mem_univ, true_and] using h

/-- **A delta sum.**  The sum of a family supported at a single point is the value at that
point. -/
theorem delta_sum {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Type*} [AddCommMonoid M]
    (a : ι) (f : ι → M) :
    (∑ k, (if a = k then f k else 0)) = f a := by
  classical
  have h := Finset.sum_ite_eq (Finset.univ : Finset ι) a f
  simpa only [Finset.mem_univ, true_and, ite_true] using h

/-- **A delta sum against a function.** -/
theorem delta_sum_mul {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Type*}
    [NonUnitalNonAssocSemiring M]
    (a : ι) (c : M) (f : ι → M) :
    (∑ k, (if a = k then c else 0) * f k) = c * f a := by
  classical
  have hstep : (∑ k, (if a = k then c else 0) * f k)
      = ∑ k, (if a = k then c * f k else 0) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : a = k <;> simp [hk]
  rw [hstep]
  have h := Finset.sum_ite_eq (Finset.univ : Finset ι) a (fun k => c * f k)
  simpa only [Finset.mem_univ, true_and, ite_true] using h

/-- **The Cauchy–Binet formula for a sum of matrices, in the `n`-tuple form.**

The determinant of a sum `∑_r κ_r A_r` of `n × n` matrices is the sum, over the `n`-tuples
`f : Fin n → ι` of summation indices, of the product `∏_j κ_{f j}` times the determinant of the
matrix whose `(p, i)`-entry is `A_{f i} p i`.

This is the elementary manifestation of the multilinearity of the determinant in the summands: it
is proved by expanding the Leibniz formula of `∑_r κ_r A_r` and rearranging the resulting finite
sums, and it holds over any commutative ring.

* `Matrix.det_sum_eq_sum_tuples` - the tuple form of the formula. -/
theorem det_sum_eq_sum_tuples (A : ι → Matrix (Fin n) (Fin n) R) (κ : ι → R) :
    (∑ r, κ r • A r).det = ∑ f : Fin n → ι, (∏ j, κ (f j)) * det (fun p i => A (f i) p i) := by
  classical
  rw [det_apply']
  -- the entries of the sum
  have hentry : ∀ (σ : Perm (Fin n)) (i : Fin n),
      (∑ r, κ r • A r) (σ i) i = ∑ r, κ r * A r (σ i) i := by
    intro σ i
    have h1 : (∑ r, κ r • A r) (σ i) = ∑ r, (κ r • A r) (σ i) :=
      fintype_sum_apply (M := fun _ => Fin n → R) (σ i) (fun r => κ r • A r)
    rw [h1]
    have h2 : (∑ r, (κ r • A r) (σ i)) i = ∑ r, ((κ r • A r) (σ i)) i :=
      fintype_sum_apply (M := fun _ => R) i (fun r => (κ r • A r) (σ i))
    rw [h2]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp [smul_eq_mul]
  -- the product over the rows: a sum over tuples
  have hprod : ∀ (σ : Perm (Fin n)), (∏ i, ∑ r, κ r * A r (σ i) i)
      = ∑ f : Fin n → ι, ∏ i, κ (f i) * A (f i) (σ i) i := by
    intro σ
    rw [Fintype.prod_sum]
  simp_rw [hentry, hprod]
  -- pull the sign inside the inner sum
  have hmul : ∀ (σ : Perm (Fin n)),
      ε σ * (∑ f : Fin n → ι, ∏ i, κ (f i) * A (f i) (σ i) i)
        = ∑ f : Fin n → ι, ε σ * (∏ i, κ (f i) * A (f i) (σ i) i) := by
    intro σ
    rw [fintype_mul_sum]
  simp_rw [hmul]
  -- regroup: the tuple index is now the outer sum
  rw [fintype_sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  -- factor the rates out of the permutation sum
  have hsplit : ∀ (σ : Perm (Fin n)),
      (∏ i, κ (f i) * A (f i) (σ i) i) = (∏ i, κ (f i)) * ∏ i, A (f i) (σ i) i := by
    intro σ
    rw [fintype_prod_mul_distrib]
  simp_rw [hsplit]
  have hfactor : (∑ σ : Perm (Fin n), ε σ * ((∏ i, κ (f i)) * ∏ i, A (f i) (σ i) i))
      = (∏ i, κ (f i)) * (∑ σ : Perm (Fin n), ε σ * ∏ i, A (f i) (σ i) i) := by
    have h := Finset.mul_sum (s := (Finset.univ : Finset (Perm (Fin n))))
      (f := fun σ => ε σ * ∏ i, A (f i) (σ i) i) (a := (∏ i, κ (f i)))
    have h' : (∏ i, κ (f i)) * (∑ σ : Perm (Fin n), ε σ * ∏ i, A (f i) (σ i) i)
        = ∑ σ : Perm (Fin n), (∏ i, κ (f i)) * (ε σ * ∏ i, A (f i) (σ i) i) := by
      simpa only [Finset.mem_univ, true_and] using h
    rw [h']
    refine Finset.sum_congr rfl fun σ _ => ?_
    ring
  rw [hfactor]
  -- the remaining permutation sum is a determinant
  rw [det_apply' (fun p i => A (f i) p i)]

/-- **The Cauchy–Binet formula in the subset form, with the diagonal of the rates split off.**

For `U : Matrix (Fin m) (Fin n)`, `W : Matrix (Fin n) (Fin m) R` and a rate function
`κ : Fin n → R`,

```
det (U * (diag κ * W)) = ∑ S, det (U restricted to S) * (∏_{r ∈ S} κ r) * det (W restricted to S)
```

where the sum is over the `m`-element subsets `S` of `Fin n` and the restrictions are to the
*increasing enumeration* of `S`.

This is the classical Cauchy–Binet formula: the determinant of a product of a rectangular and a
transpose-rectangular matrix is the sum, over the `m`-element subsets of the inner index set, of
the products of the corresponding minors.  The rate constants enter as a *product*, one factor per
reaction of the subset.

* `Matrix.det_mul_diag_mul_eq_sum_subsets` - the subset form of the formula. -/
theorem det_mul_diag_mul_eq_sum_subsets (U : Matrix (Fin m) (Fin n) R) (W : Matrix (Fin n) (Fin m) R)
    (κ : Fin n → R) :
    (U * (Matrix.diagonal κ * W)).det
      = ∑ S ∈ ((Finset.univ : Finset (Fin n)).powersetCard m).attach,
        (U.submatrix id (S.1.orderEmbOfFin (Finset.mem_powersetCard.mp S.2).2)).det
          * (∏ i, κ (S.1.orderEmbOfFin (Finset.mem_powersetCard.mp S.2).2 i))
          * (W.submatrix (S.1.orderEmbOfFin (Finset.mem_powersetCard.mp S.2).2) id).det := by
  classical
  have h := det_mul_eq_sum_powersetCard U (Matrix.diagonal κ * W)
  rw [h]
  refine Finset.sum_congr rfl fun S _ => ?_
  have hS : S.1.card = m := (Finset.mem_powersetCard.mp S.2).2
  -- the diagonal of the rates splits off the minor of `W`
  have h1 : (Matrix.diagonal κ * W).submatrix (S.1.orderEmbOfFin hS) id
      = Matrix.diagonal (fun i => κ (S.1.orderEmbOfFin hS i)) *
        (W.submatrix (S.1.orderEmbOfFin hS) id) := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.diagonal_apply]
    rw [delta_sum_mul (S.1.orderEmbOfFin hS i) (κ (S.1.orderEmbOfFin hS i))
      (fun k => W k (id j))]
    rw [delta_sum_mul i (κ (S.1.orderEmbOfFin hS i))
      (fun k => W (S.1.orderEmbOfFin hS k) (id j))]
  have hdet : ((Matrix.diagonal κ * W).submatrix (S.1.orderEmbOfFin hS) id).det
      = (∏ i, κ (S.1.orderEmbOfFin hS i)) *
        (W.submatrix (S.1.orderEmbOfFin hS) id).det := by
    rw [h1, Matrix.det_mul, Matrix.det_diagonal]
  rw [hdet]
  ring

end Matrix

namespace CRNT

namespace Network

open scoped BigOperators
open Module

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ## 2. The chart data of a network -/

/-- **The chart gradient of a reaction.**  The `j`-th entry is the directional derivative of the
source monomial of the reaction along the `j`-th chart direction. -/
noncomputable def chartGradient (N : Network S) (chart : (Fin N.stoichRank → ℝ) →L[ℝ] (S → ℝ))
    (x : Concentration S) (r : N.R) : Fin N.stoichRank → ℝ :=
  fun j => ∑ k, massActionMonomialGrad (N.reaction r).source x k * (chart (Pi.single j 1)) k

/-- **The chart reaction vector.**  The reaction vector of the reaction, in chart coordinates. -/
noncomputable def chartVector (N : Network S) (proj : (S → ℝ) →L[ℝ] (Fin N.stoichRank → ℝ))
    (r : N.R) : Fin N.stoichRank → ℝ :=
  fun j => proj (N.reactionVector r) j

/-- **The mass-action Jacobian operator with raw rate constants.** -/
noncomputable def massActionJacobianCLMWith (N : Network S) (κ : N.R → ℝ) (x : Concentration S) :
    Concentration S →L[ℝ] Concentration S :=
  ∑ (r : N.R), (κ r • (∑ j, massActionMonomialGrad (N.reaction r).source x j •
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : S => ℝ) j)).smulRight (N.reactionVector r)

/-- **The mass-action Jacobian with raw rate constants agrees with the repository's version.** -/
theorem massActionJacobianCLMWith_eq (N : Network S) (κ : N.RateConstants) (x : Concentration S) :
    N.massActionJacobianCLMWith κ.k x = N.massActionJacobianCLM κ x := rfl

/-- **The reduced Jacobian in an arbitrary chart of the stoichiometric subspace.**  The chart
`chart` and its dual projection `proj` replace the repository's canonical `Network.stoichChart`
and `Network.stoichProj`. -/
noncomputable def reducedJacobianInChart (N : Network S)
    (chart : (Fin N.stoichRank → ℝ) →L[ℝ] (S → ℝ))
    (proj : (S → ℝ) →L[ℝ] (Fin N.stoichRank → ℝ))
    (κ : N.R → ℝ) (x : Concentration S) : Matrix (Fin N.stoichRank) (Fin N.stoichRank) ℝ :=
  jacobianMatrix (proj.comp ((N.massActionJacobianCLMWith κ x).comp chart))

/-- **The mass-action Jacobian with raw rate constants, as a sum of species vectors.** -/
theorem massActionJacobianCLMWith_apply (N : Network S) (κ : N.R → ℝ) (x : Concentration S)
    (w : Concentration S) :
    N.massActionJacobianCLMWith κ x w
      = ∑ r, ((κ r * (∑ j, massActionMonomialGrad (N.reaction r).source x j * w j)) •
          (N.reactionVector r)) := by
  simp only [massActionJacobianCLMWith, sum_apply, ContinuousLinearMap.smulRight_apply,
    smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]

/-- **The entries of the reduced Jacobian.**  The reduced Jacobian in a chart is the sum, over
the reactions, of the rate constant times the chart gradient times the chart reaction vector:
the rank-one structure that the Cauchy–Binet expansion exploits. -/
theorem reducedJacobianInChart_apply (N : Network S)
    (chart : (Fin N.stoichRank → ℝ) →L[ℝ] (S → ℝ))
    (proj : (S → ℝ) →L[ℝ] (Fin N.stoichRank → ℝ))
    (κ : N.R → ℝ) (x : Concentration S) (i j : Fin N.stoichRank) :
    N.reducedJacobianInChart chart proj κ x i j
      = ∑ r, κ r * (chartGradient N chart x r j) * (chartVector N proj r i) := by
  have h1 : N.reducedJacobianInChart chart proj κ x i j
      = proj (N.massActionJacobianCLMWith κ x (chart (Pi.single j 1))) i := by
    simp only [reducedJacobianInChart, jacobianMatrix, LinearMap.toMatrix'_apply]
    rfl
  rw [h1]
  -- the projection of a sum is the sum of the projections
  let hproj : (S → ℝ) →+ (Fin N.stoichRank → ℝ) :=
    { toFun := fun z => proj z
      map_zero' := by simp
      map_add' := fun a b => by rw [map_add] }
  rw [massActionJacobianCLMWith_apply]
  set F : N.R → (S → ℝ) := fun r =>
    ((κ r * (∑ k, massActionMonomialGrad (N.reaction r).source x k *
      (chart (Pi.single j 1)) k)) • (N.reactionVector r)) with hF
  have hsum : proj (∑ r, F r) i = ∑ r, proj (F r) i := by
    calc proj (∑ r, F r) i = hproj (∑ r, F r) i := rfl
      _ = (∑ r, hproj (F r)) i := by
          rw [map_sum hproj F (Finset.univ : Finset N.R)]
      _ = ∑ r, hproj (F r) i := by
          exact Finset.sum_apply i (Finset.univ : Finset N.R)
            (fun r (i : Fin N.stoichRank) => hproj (F r) i)
      _ = ∑ r, proj (F r) i := rfl
  rw [hsum]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [hF]
  have hg : (∑ k, massActionMonomialGrad (N.reaction r).source x k *
        (chart (Pi.single j 1)) k)
      = chartGradient N chart x r j := rfl
  rw [hg]
  simp only [map_smul, Pi.smul_apply, smul_eq_mul]
  rfl

/-! ## 3. The circuit and gradient matrices -/

/-- **The circuit matrix of a list of reactions.**  The columns of the matrix are the *chart
reaction vectors* of the reactions `f 0, …, f (s-1)`.  Its determinant vanishes exactly when
those reaction vectors are linearly dependent — that is, when the reactions carry a circuit. -/
noncomputable def circuitMatrix (N : Network S) (proj : (S → ℝ) →L[ℝ] (Fin N.stoichRank → ℝ))
    (f : Fin N.stoichRank → N.R) : Matrix (Fin N.stoichRank) (Fin N.stoichRank) ℝ :=
  fun i j => chartVector N proj (f j) i

/-- **The gradient matrix of a list of reactions.**  The rows of the matrix are the *chart
gradients* of the reactions `f 0, …, f (s-1)`. -/
noncomputable def gradientMatrix (N : Network S) (chart : (Fin N.stoichRank → ℝ) →L[ℝ] (S → ℝ))
    (x : Concentration S) (f : Fin N.stoichRank → N.R) :
    Matrix (Fin N.stoichRank) (Fin N.stoichRank) ℝ :=
  fun i j => chartGradient N chart x (f i) j

/-- **The enumeration of the reactions of an `s`-element subset of the labelled reactions.** -/
noncomputable def subsetReactions (N : Network S) (e : N.R ≃ Fin m) (T : Finset (Fin m))
    (hT : T.card = N.stoichRank) : Fin N.stoichRank → N.R :=
  fun j => e.symm (T.orderEmbOfFin hT j)

/-! ## 4. The Cauchy–Binet expansion of the reduced determinant -/

/-- **The Cauchy–Binet expansion of the reduced determinant.**

The determinant of the reduced Jacobian of a network of stoichiometric rank `s` is the sum, over
the `s`-element subsets `S` of the reactions, of

* the determinant of the **circuit matrix** of `S` — the determinant of the matrix whose columns
  are the chart reaction vectors of the reactions of `S`;
* the **product of the rate constants** `∏_{r ∈ S} κ r`;
* the determinant of the **gradient matrix** of `S` — the determinant of the matrix whose rows are
  the chart gradients of the reactions of `S`.

This is the classical Cauchy–Binet formula applied to the factorization
`M = V * (diag κ * G)` of the reduced Jacobian into the matrix of chart reaction vectors and the
matrix of chart gradients.  Each term is a *product of `s` rate constants* — in contrast to the
rank-one case, where the reduced determinant is an *affine* function of the rate constants
(`CRNT.Network.not_eq_rateProduct_mul`).

* `Network.reducedJacobianInChart_det_eq_cauchyBinet` - the Cauchy–Binet expansion. -/
theorem reducedJacobianInChart_det_eq_cauchyBinet (N : Network S) (m : ℕ) (e : N.R ≃ Fin m)
    (chart : (Fin N.stoichRank → ℝ) →L[ℝ] (S → ℝ))
    (proj : (S → ℝ) →L[ℝ] (Fin N.stoichRank → ℝ))
    (κ : N.R → ℝ) (x : Concentration S) :
    (N.reducedJacobianInChart chart proj κ x).det
      = ∑ S ∈ ((Finset.univ : Finset (Fin m)).powersetCard N.stoichRank).attach,
        (circuitMatrix N proj
          (subsetReactions N e S.1 (Finset.mem_powersetCard.mp S.2).2)).det
          * (∏ j, κ (subsetReactions N e S.1 (Finset.mem_powersetCard.mp S.2).2 j))
          * (gradientMatrix N chart x
            (subsetReactions N e S.1 (Finset.mem_powersetCard.mp S.2).2)).det := by
  -- the two matrices of the factorization
  let V : Matrix (Fin N.stoichRank) (Fin m) ℝ := fun i r => chartVector N proj (e.symm r) i
  let G : Matrix (Fin m) (Fin N.stoichRank) ℝ := fun r j => chartGradient N chart x (e.symm r) j
  let κ' : Fin m → ℝ := fun r => κ (e.symm r)
  -- the reduced Jacobian is `V * (diag κ' * G)`
  have hM : N.reducedJacobianInChart chart proj κ x
      = V * (Matrix.diagonal κ' * G) := by
    ext i j
    rw [reducedJacobianInChart_apply]
    simp only [Matrix.mul_apply]
    have hconv : (∑ (r : N.R), κ r * (chartGradient N chart x r j) * (chartVector N proj r i))
        = ∑ (s : Fin m), κ (e.symm s) * (chartGradient N chart x (e.symm s) j) *
            (chartVector N proj (e.symm s) i) := by
      symm
      exact Fintype.sum_equiv e.symm
        (fun s : Fin m => κ (e.symm s) * (chartGradient N chart x (e.symm s) j) *
          (chartVector N proj (e.symm s) i))
        (fun r : N.R => κ r * (chartGradient N chart x r j) * (chartVector N proj r i))
        (fun s => rfl)
    rw [hconv]
    refine Finset.sum_congr rfl fun r _ => ?_
    have hd : ∑ j_1, Matrix.diagonal κ' r j_1 * G j_1 j = κ' r * G r j := by
      simp only [Matrix.diagonal_apply]
      exact Matrix.delta_sum_mul r (κ' r) (fun k => G k j)
    have hV : V i r = chartVector N proj (e.symm r) i := rfl
    have hG : G r j = chartGradient N chart x (e.symm r) j := rfl
    have hκ : κ' r = κ (e.symm r) := rfl
    rw [hd, hV, hG, hκ]
    ring
  rw [hM]
  rw [Matrix.det_mul_diag_mul_eq_sum_subsets]
  -- identify the two minors
  refine Finset.sum_congr rfl fun S _ => ?_
  have hS : S.1.card = N.stoichRank := (Finset.mem_powersetCard.mp S.2).2
  have hV' : V.submatrix id (S.1.orderEmbOfFin hS)
      = circuitMatrix N proj (subsetReactions N e S.1 hS) := by
    ext i j
    rfl
  have hG' : G.submatrix (S.1.orderEmbOfFin hS) id
      = gradientMatrix N chart x (subsetReactions N e S.1 hS) := by
    ext i j
    rfl
  rw [hV', hG']
  rfl

/-! ## 5. The circuit reading -/

/-- **A positive circuit of a network.**  A set of reactions whose *reaction vectors* admit a
positive linear dependence: there are coefficients `lam r > 0` on the reactions of the set, zero
off it, with `∑_r lam r • (reactionVector r) = 0`.  This is the classical reaction-network
notion of a *circuit*. -/
def IsPositiveCircuit (N : Network S) (C : Finset N.R) : Prop :=
  ∃ lam : N.R → ℝ, (∀ r, r ∈ C → 0 < lam r) ∧ (∀ r, r ∉ C → lam r = 0) ∧
    ∑ r, lam r • (N.reactionVector r) = 0

/-- **The chart vectors of a circuit are positively dependent.**  The dual projection is linear,
so a positive dependence among the reaction vectors gives one among the chart reaction vectors. -/
theorem chartVector_positiveDep_of_circuit (N : Network S)
    (proj : (S → ℝ) →L[ℝ] (Fin N.stoichRank → ℝ)) (C : Finset N.R)
    (hC : N.IsPositiveCircuit C) :
    ∃ lam : N.R → ℝ, (∀ r, r ∈ C → 0 < lam r) ∧ (∀ r, r ∉ C → lam r = 0) ∧
      ∑ r, lam r • (chartVector N proj r) = 0 := by
  obtain ⟨lam, hlam, hzero, hsum⟩ := hC
  refine ⟨lam, hlam, hzero, ?_⟩
  have h1 : (∑ r, lam r • (N.reactionVector r)) = 0 := hsum
  have h2 : (∑ r, lam r • (chartVector N proj r))
      = proj (∑ r, lam r • (N.reactionVector r)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [map_smul]
    rfl
  rw [h2, h1]
  simp [map_zero]

/-- **A Cauchy–Binet term vanishes as soon as its reactions are linearly dependent.**  If the
reaction vectors of the reactions `f 0, …, f (s-1)` satisfy a nontrivial linear dependence
(`c` a `Finsupp` of coefficients with `Finsupp.linearCombination ℝ (fun j => reactionVector (f j)) c
= 0` and `c ≠ 0`), then the *circuit matrix* — the matrix whose columns are the chart reaction
vectors of those reactions — is singular, and the corresponding Cauchy–Binet term contributes
nothing. -/
theorem circuitMatrix_det_eq_zero_of_dep (N : Network S)
    (proj : (S → ℝ) →L[ℝ] (Fin N.stoichRank → ℝ)) (f : Fin N.stoichRank → N.R)
    (c : Finsupp (Fin N.stoichRank) ℝ) (hc : c ≠ 0)
    (hdep : Finsupp.linearCombination ℝ (fun j => N.reactionVector (f j)) c = 0) :
    (circuitMatrix N proj f).det = 0 := by
  have hnotind : ¬ LinearIndependent ℝ (circuitMatrix N proj f).col := by
    intro hli
    have h1 : Finsupp.linearCombination ℝ (fun j => chartVector N proj (f j)) c = 0 := by
      have h2 := Finsupp.apply_linearCombination ℝ (proj.toLinearMap)
        (fun j => N.reactionVector (f j)) c
      have h3 : proj.toLinearMap ∘ (fun j => N.reactionVector (f j))
          = (fun j => chartVector N proj (f j)) := by
        funext j
        rfl
      rw [h3] at h2
      rw [← h2, hdep]
      simp
    have h5 : Finsupp.linearCombination ℝ (circuitMatrix N proj f).col 0 = 0 := by simp
    have h6 : Finsupp.linearCombination ℝ (circuitMatrix N proj f).col c
        = Finsupp.linearCombination ℝ (circuitMatrix N proj f).col 0 := by
      have h7 : Finsupp.linearCombination ℝ (circuitMatrix N proj f).col c
          = Finsupp.linearCombination ℝ (fun j => chartVector N proj (f j)) c := rfl
      rw [← h7] at h1
      exact h1.trans h5.symm
    exact absurd (hli h6) hc
  exact Matrix.det_eq_zero_of_not_linearIndependent_cols hnotind

/-- **A Cauchy–Binet term vanishes as soon as its subset contains a circuit.**  This is the
circuit reading of the Cauchy–Binet expansion: a configuration of `s` reactions carrying a
circuit contributes nothing to the reduced determinant. -/
theorem circuitMatrix_det_eq_zero_of_circuit (N : Network S)
    (proj : (S → ℝ) →L[ℝ] (Fin N.stoichRank → ℝ)) (f : Fin N.stoichRank → N.R)
    (hinj : Function.Injective f) (C : Finset N.R) (hC : N.IsPositiveCircuit C)
    (hCne : C.Nonempty) (hsub : ∀ r : N.R, r ∈ C → ∃ j, f j = r) :
    (circuitMatrix N proj f).det = 0 := by
  have hC' := hC
  obtain ⟨lam, hlam, hzero, hsum⟩ := hC'
  -- the dependence of the reaction vectors along `f`
  have hdep : ∑ j, lam (f j) • (N.reactionVector (f j)) = 0 := by
    have h1 : (∑ j, lam (f j) • (N.reactionVector (f j)))
        = ∑ r ∈ Finset.univ.image f, lam r • (N.reactionVector r) := by
      rw [Finset.sum_image (ι := N.R) (κ := Fin N.stoichRank)
        (s := (Finset.univ : Finset (Fin N.stoichRank))) (g := f) (by
          intro a _ b _ hab
          exact hinj hab)]
    have h2 : (∑ r ∈ Finset.univ.image f, lam r • (N.reactionVector r))
        = ∑ r, lam r • (N.reactionVector r) := by
      refine Finset.sum_subset (s₁ := Finset.univ.image f) (s₂ := (Finset.univ : Finset N.R))
        (Finset.subset_univ _) (fun r _ hr2 => ?_)
      by_cases hrc : r ∈ C
      · obtain ⟨j, hj⟩ := hsub r hrc
        have hmem : r ∈ Finset.univ.image f := Finset.mem_image.mpr ⟨j, Finset.mem_univ j, hj⟩
        exact (hr2 hmem).elim
      · rw [hzero r hrc]
        simp
    rw [h1, h2, hsum]
  -- the coefficients are not all zero
  have hne : ∃ j, lam (f j) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨r, hr⟩ := hCne
    obtain ⟨j, hj⟩ := hsub r hr
    have hlam0 : lam r = 0 := by rw [← hj]; exact hcon j
    have hpos : 0 < lam r := hlam r hr
    linarith
  -- the corresponding `Finsupp` of coefficients
  set c : Finsupp (Fin N.stoichRank) ℝ :=
    Finsupp.onFinset (Finset.univ : Finset (Fin N.stoichRank)) (fun j => lam (f j))
      (fun j _ => Finset.mem_univ j) with hc
  have hcne : c ≠ 0 := by
    obtain ⟨j, hj⟩ := hne
    intro hcz
    have hj' : c j = 0 := by
      rw [hcz]
      simp
    have hlamj : lam (f j) = 0 := by
      rw [hc] at hj'
      simpa using hj'
    rw [hlamj] at hj
    exact hj rfl
  have hcomb : Finsupp.linearCombination ℝ (fun j => N.reactionVector (f j)) c = 0 := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    · exact hdep
    · intro i
      simp
  exact circuitMatrix_det_eq_zero_of_dep N proj f c hcne hcomb

/-! ## 6. A rank-two instance -/

/-- **The chart reaction vectors of a rank-two instance.**  The columns are the chart images of
the reaction vectors of the four reactions `A → B`, `B → A`, `B → C`, `C → A` of a rank-two
network on the species `A`, `B`, `C`, in the chart with basis `A → B` and `B → C`.  The first two
columns are opposite: the pair `{A → B, B → A}` is a **circuit**. -/
def exU : Matrix (Fin 2) (Fin 4) ℝ := ![![1, -1, 0, -1], ![0, 0, 1, -1]]

/-- **The chart gradients of the rank-two instance.**  The rows are the chart gradients of the
source monomials of the four reactions `A → B` (source `A`), `B → A` (source `B`), `B → C`
(source `B`) and `C → A` (source `C`). -/
def exG : Matrix (Fin 4) (Fin 2) ℝ := ![![-1, 0], ![1, -1], ![1, -1], ![0, 1]]

/-- **The rate constants of the rank-two instance.** -/
def exκ : Fin 4 → ℝ := ![2, 3, 5, 7]

/-- **The increasing enumeration of the pair `{0, 1}`.** -/
def exe01 : Fin 2 → Fin 4 := fun i => if i = 0 then 0 else 1

/-- **The increasing enumeration of the pair `{0, 2}`.** -/
def exe02 : Fin 2 → Fin 4 := fun i => if i = 0 then 0 else 2

/-- **The increasing enumeration of the pair `{1, 3}`.** -/
def exe13 : Fin 2 → Fin 4 := fun i => if i = 0 then 1 else 3

/-- **The reduced determinant of the rank-two instance.**  The determinant of the reduced
Jacobian of the instance is `80`. -/
theorem ex_det : (exU * (Matrix.diagonal exκ * exG)).det = 80 := by
  rw [Matrix.det_fin_two]
  simp only [Matrix.mul_apply]
  norm_num [exU, exG, exκ, Matrix.diagonal_apply, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

/-- **The Cauchy–Binet sum of the rank-two instance.**  The determinant of the reduced Jacobian
is the sum, over the six pairs of reactions, of the product of the two rate constants times the
two minors; the sum is `80`, the same value as the direct determinant
(`Network.ex_det`). -/
theorem ex_cauchyBinet :
    (∑ S ∈ ((Finset.univ : Finset (Fin 4)).powersetCard 2).attach,
      (exU.submatrix id (S.1.orderEmbOfFin (Finset.mem_powersetCard.mp S.2).2)).det
        * (∏ i, exκ (S.1.orderEmbOfFin (Finset.mem_powersetCard.mp S.2).2 i))
        * (exG.submatrix (S.1.orderEmbOfFin (Finset.mem_powersetCard.mp S.2).2) id).det) = 80 := by
  rw [← Matrix.det_mul_diag_mul_eq_sum_subsets]
  exact ex_det

/-- **The circuit pair of the rank-two instance contributes nothing.**  The pair
`{A → B, B → A}` is a circuit: its two chart reaction vectors are opposite, so the circuit
matrix of the pair is singular and the corresponding Cauchy–Binet term vanishes. -/
theorem ex_circuit_pair :
    (exU.submatrix id exe01).det = 0 := by
  rw [Matrix.det_fin_two]
  simp only [Matrix.submatrix_apply]
  norm_num [exU, exe01, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.eq_zero,
    Fin.succ_ne_zero, Fin.zero_eta]

/-- **A non-circuit pair of the rank-two instance contributes the product of its two rate
constants.**  The pair `{A → B, B → C}` contributes `κ₀ κ₂ = 2 · 5 = 10`. -/
theorem ex_pair_02 :
    (exU.submatrix id exe02).det * (exκ 0 * exκ 2) * (exG.submatrix exe02 id).det = 10 := by
  rw [Matrix.det_fin_two]
  simp only [Matrix.submatrix_apply]
  rw [Matrix.det_fin_two]
  simp only [Matrix.submatrix_apply]
  norm_num [exU, exG, exκ, exe02, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.eq_zero,
    Fin.succ_ne_zero, Fin.zero_eta]

/-- **Another non-circuit pair of the rank-two instance contributes the product of its two rate
constants.**  The pair `{B → A, C → A}` contributes `κ₁ κ₃ = 3 · 7 = 21`. -/
theorem ex_pair_13 :
    (exU.submatrix id exe13).det * (exκ 1 * exκ 3) * (exG.submatrix exe13 id).det = 21 := by
  rw [Matrix.det_fin_two]
  simp only [Matrix.submatrix_apply]
  rw [Matrix.det_fin_two]
  simp only [Matrix.submatrix_apply]
  norm_num [exU, exG, exκ, exe13, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.eq_zero,
    Fin.succ_ne_zero, Fin.zero_eta]

/-! ## 7. The canonical chart of the repository -/

/-- **The canonical chart.**  The reduced Jacobian of the repository is the reduced Jacobian in
the canonical chart of the stoichiometric subspace, `Network.stoichChart` and its dual
`Network.stoichProj`. -/
theorem reducedJacobian_eq_reducedJacobianInChart (N : Network S) (κ : N.RateConstants)
    (x₀ : Concentration S) (y : Fin N.stoichRank → ℝ) :
    N.reducedJacobian κ x₀ y
      = N.reducedJacobianInChart N.stoichChart N.stoichProj κ.k (N.affineChart x₀ y) := rfl

/-- **The Cauchy–Binet expansion of the reduced determinant in the canonical chart.**  The
determinant of the reduced Jacobian of a network of stoichiometric rank `s` is the sum, over the
`s`-element subsets `S` of the reactions, of the determinant of the circuit matrix of `S` (the
matrix whose columns are the chart reaction vectors of the reactions of `S`), the product of the
rate constants of the reactions of `S`, and the determinant of the gradient matrix of `S` (the
matrix whose rows are the chart gradients of the reactions of `S`). -/
theorem reducedJacobian_det_eq_cauchyBinet (N : Network S) (κ : N.RateConstants)
    (x₀ : Concentration S) (y : Fin N.stoichRank → ℝ) :
    (N.reducedJacobian κ x₀ y).det
      = ∑ S ∈ ((Finset.univ : Finset (Fin (Fintype.card N.R))).powersetCard N.stoichRank).attach,
        (circuitMatrix N N.stoichProj
          (subsetReactions N (Fintype.equivFin N.R) S.1
            (Finset.mem_powersetCard.mp S.2).2)).det
          * (∏ j, κ.k (subsetReactions N (Fintype.equivFin N.R) S.1
              (Finset.mem_powersetCard.mp S.2).2 j))
          * (gradientMatrix N N.stoichChart (N.affineChart x₀ y)
              (subsetReactions N (Fintype.equivFin N.R) S.1
                (Finset.mem_powersetCard.mp S.2).2)).det := by
  rw [reducedJacobian_eq_reducedJacobianInChart]
  exact reducedJacobianInChart_det_eq_cauchyBinet N (Fintype.card N.R) (Fintype.equivFin N.R)
    N.stoichChart N.stoichProj κ.k (N.affineChart x₀ y)

end Network

end CRNT
