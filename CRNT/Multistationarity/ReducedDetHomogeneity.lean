import CRNT.Multistationarity.ReducedDeterminantCircuits
import CRNT.Multistationarity.DegreeStructural
import Mathlib.Basic.Sign.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Nonsingular

/-!
# Degree-`s` homogeneity of the reduced determinant, the sign rule for a Cauchy–Binet term, and
# the exceptional local degree

This module completes the algebraic content of field-map leaf **M13** ("Parameter regions for
multistationarity"), on top of `CRNT.Multistationarity.ReducedDeterminantCircuits`, which
supplied the Cauchy–Binet expansion of the reduced determinant and the higher-rank circuit
reading of the multistationarity regions.

## 1. The setting: the Cauchy–Binet expansion and the higher-rank circuit reading

For a network `N` of stoichiometric rank `s`, the reduced Jacobian, read in a chart of the
stoichiometric subspace, is the rank-one sum

```
M = V * (diag κ * G),
```

where `V` is the matrix of the *chart reaction vectors* `proj (reactionVector r)` and `G` the
matrix of the *chart gradients* `∇ (source monomial of r)`.  The classical Cauchy–Binet formula
expands its determinant (`Network.reducedJacobianInChart_det_eq_cauchyBinet`,
`Network.reducedJacobian_det_eq_cauchyBinet`):

```
det M = ∑_{S, |S| = s}  det(circuit matrix of S) * (∏_{r ∈ S} κ_r) * det(gradient matrix of S).
```

Every term is a **product of `s` rate constants** — one per reaction of the supporting subset —
weighted by two minors.  This is the higher-rank circuit reading of the parameter regions of
multistationarity of Conradi–Feliu–Mincheva–Wiuf, *A characterization of multistationarity in
chemical reaction networks* (Proc. Natl. Acad. Sci. USA **108** (2011) 2853–2858), Theorem 1:
in dimension `s ≥ 2` the multistationarity region is described by the sign of a *sum* of such
products, and not by the sign of a single product as in rank one.

## 2. The degree-`s` homogeneity of the reduced determinant

`Network.reducedJacobianInChart_det_scale` and `Network.reducedJacobian_det_scale`: the reduced
determinant is **homogeneous of degree `s`** in the rate constants; scaling every rate constant
by `λ` scales the reduced determinant by `λ^s`.  Since every Cauchy–Binet term is a product of
exactly `s` rate constants, this is immediate from the expansion; the proof given here is the
entrywise one (the reduced Jacobian matrix becomes `λ • M`).

Two consequences:

* `Network.sign_reducedJacobian_det_eq_of_scale`: for `λ > 0` the **sign** of the reduced
  determinant — the quantity that decides the multistationarity region — is *invariant* under a
  common positive rescaling of the rate constants.  The region therefore only depends on the
  *ratios* of the rate constants, as it should.
* `Network.reducedJacobian_det_scale_of_stoichRank_one`: in rank one (`s = 1`) the homogeneity
  reads `det = λ * det`, i.e. the reduced determinant is an **affine** (indeed linear) function of
  the rate constants.  This is the rank-one instance of the degree-`s` statement, and it is the
  affine counterpart of the rank-one formula `Network.reducedDerivOf_smul`
  (`CRNT.Multistationarity.MultistationarityRegionDescription`); the classical *single-product*
  reading of the rank-one reduced determinant is refuted by
  `Network.not_eq_rateProduct_mul`.

## 3. The sign rule for a Cauchy–Binet term

`Network.cauchyBinet_term_sign`: the sign of a Cauchy–Binet term
`det(circuit matrix) * (∏ κ_r) * det(gradient matrix)` is the **product of the signs of the two
minors**; the rate product contributes `+1`, because all rate constants are positive.  Together
with the expansion of §1 this is the sign rule of the higher-rank circuit reading: a term is
*positive* exactly when the two minors have the same sign, *negative* when they have opposite
signs, and it *vanishes* exactly when one of the two minors vanishes.

## 4. The converse characterisation of the non-vanishing terms

`Network.circuitMatrix_det_ne_zero_iff_chartVectors_linearIndependent`: a Cauchy–Binet term is
**nonzero exactly when the chart reaction vectors of the reactions of the supporting subset are
linearly independent** — equivalently, when the circuit matrix of the subset is invertible.  This
is the converse half of the reading; the direct half (`Network.circuitMatrix_det_eq_zero_of_dep`
and `Network.circuitMatrix_det_eq_zero_of_circuit`) was already formalized.

The chart–projection compatibility `chart (proj (reactionVector r)) = reactionVector r`, which the
leaf's notes list as a hypothesis of the converse characterisation, is **automatic for the
canonical chart**: the reaction vector lies in the stoichiometric subspace, so
`Network.stoichChart_stoichProj_reactionVector` holds without hypotheses.  The characterisation
of §4 is therefore unconditional for the canonical chart of the repository.

## 5. The exceptional local degree is the sign of the Cauchy–Binet sum

`Network.localDegree_eq_one_iff_reducedDet_pos`: the **local degree** of the steady-state map at
a steady state of the class is `+1` exactly when the reduced determinant there is positive.  The
reduced determinant *is* the Cauchy–Binet sum (§1), so
`Network.localDegree_eq_one_iff_cauchyBinet_sum_pos` is the same statement with the Cauchy–Binet
sum written out: the local degree is `+1` exactly when the Cauchy–Binet sum is positive.  This is
the point where the algebraic content of §1–§4 meets the degree theory of
`CRNT.Multistationarity.DegreeStructural`: the sign of the Cauchy–Binet sum is the local degree
of the steady-state map, and hence the summand of the class degree.

## 6. Orientation of the circuit reading (important)

A **circuit makes a Cauchy–Binet minor VANISH**.  The circuit matrix of a subset carrying a
circuit is singular (`Network.circuitMatrix_det_eq_zero_of_circuit`,
`Network.circuitMatrix_det_eq_zero_of_dep`), so the corresponding term of the expansion
contributes **nothing**.  The frequently quoted framing "the non-vanishing terms are exactly the
circuits" is **inverted**: the terms that *survive* are those whose supporting subset is free of
circuits, i.e. those whose chart reaction vectors are linearly independent
(`Network.circuitMatrix_det_ne_zero_iff_chartVectors_linearIndependent`).  The repository follows
the correct statement.

## 7. What remains open

* An explicit *description* of the multistationarity region in rank `s ≥ 2` (as a semialgebraic
  set in the space of rate constants) is not attempted here; what is formalized is the algebraic
  structure of the reduced determinant whose sign decides the region.
* The Conradi–Feliu–Mincheva–Wiuf conclusion "positive reduced determinant ⇒ *two* positive
  steady states" in dimension `s ≥ 2` needs the homotopy argument on the perturbed map; this
  module provides only the local-degree half (`Network.localDegree_eq_one_iff_reducedDet_pos`),
  the class-degree machinery being in `CRNT.Multistationarity.DegreeExistence` and
  `CRNT.Multistationarity.DegreeStructural`.

Depends on: `CRNT.Multistationarity.ReducedDeterminantCircuits`,
`CRNT.Multistationarity.DegreeStructural`.
-/

namespace CRNT

namespace Network

open scoped BigOperators
open Module

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ## 1. The degree-`s` homogeneity of the reduced determinant -/

/-- **The reduced determinant is homogeneous of degree `s = stoichRank` in the rate constants.**
In rank one the reduced determinant is affine in the rates; in rank `s` it is a *multilinear*
object of degree `s`: every Cauchy–Binet term is a product of `s` rate constants, one per
reaction of the supporting subset, so scaling every rate by `λ` scales the reduced determinant
by `λ^s`.

The proof is entrywise: the `λ`-scaled reduced Jacobian is `λ • M` (each entry of `M` is
`∑ r, κ_r * g_r j * v_r i`, linear in the rates), and `Matrix.det_smul` gives
`det (λ • M) = λ ^ (card (Fin s)) * det M`. -/
theorem reducedJacobianInChart_det_scale
    (N : Network S)
    (chart : (Fin N.stoichRank → ℝ) →L[ℝ] (S → ℝ))
    (proj : (S → ℝ) →L[ℝ] (Fin N.stoichRank → ℝ))
    (κ : N.R → ℝ) (lam : ℝ) (x : Concentration S) :
    (N.reducedJacobianInChart chart proj (fun r => lam * κ r) x).det
      = lam ^ N.stoichRank * (N.reducedJacobianInChart chart proj κ x).det := by
  have happly (κ' : N.R → ℝ) (i j : Fin N.stoichRank) :
      N.reducedJacobianInChart chart proj κ' x i j
        = ∑ r, κ' r * (chartGradient N chart x r j) * (chartVector N proj r i) :=
    reducedJacobianInChart_apply N chart proj κ' x i j
  have hM : N.reducedJacobianInChart chart proj (fun r => lam * κ r) x
      = lam • N.reducedJacobianInChart chart proj κ x := by
    apply Matrix.ext
    intro i j
    simp only [Matrix.smul_apply, smul_eq_mul]
    rw [happly, happly]
    calc (∑ r, (lam * κ r) * (chartGradient N chart x r j) * (chartVector N proj r i))
        = ∑ r, lam * (κ r * (chartGradient N chart x r j) * (chartVector N proj r i)) := by
          refine Finset.sum_congr rfl fun r _ => ?_
          ring
      _ = lam * (∑ r, κ r * (chartGradient N chart x r j) * (chartVector N proj r i)) := by
          rw [Finset.mul_sum]
  rw [hM, Matrix.det_smul, Fintype.card_fin]

/-- **The reduced determinant of the canonical chart is homogeneous of degree `s` in the rate
constants.**  This is `Network.reducedJacobianInChart_det_scale` for the repository's own chart
`Network.stoichChart` and its dual `Network.stoichProj`: scaling every rate constant by `lam`
scales the reduced determinant by `lam ^ s`. -/
theorem reducedJacobian_det_scale (N : Network S) (κ : N.RateConstants) (lam : ℝ) (hlam : 0 < lam)
    (x₀ : Concentration S) (y : Fin N.stoichRank → ℝ) :
    (N.reducedJacobian ⟨fun r => lam * κ.k r, fun r => mul_pos hlam (κ.positive r)⟩ x₀ y).det
      = lam ^ N.stoichRank * (N.reducedJacobian κ x₀ y).det := by
  have h3 : ∀ (κ' : N.RateConstants), κ'.k = (fun r => lam * κ.k r) →
      (N.reducedJacobian κ' x₀ y).det = lam ^ N.stoichRank * (N.reducedJacobian κ x₀ y).det := by
    intro κ' hκ'
    have h1 := reducedJacobianInChart_det_scale N N.stoichChart N.stoichProj κ.k lam
      (N.affineChart x₀ y)
    rw [reducedJacobian_eq_reducedJacobianInChart, reducedJacobian_eq_reducedJacobianInChart]
    rw [hκ']
    exact h1
  exact h3 ⟨fun r => lam * κ.k r, fun r => mul_pos hlam (κ.positive r)⟩ rfl

/-- **The sign of the reduced determinant is invariant under a common positive rescaling of the
rate constants.**  The sign of the reduced determinant is the quantity that decides the
multistationarity region (Conradi–Feliu–Mincheva–Wiuf, Theorem 1); since the reduced determinant
is homogeneous of degree `s`, a *positive* common rescaling of the rates does not change it.
Hence the region depends on the rates only through their ratios. -/
theorem sign_reducedJacobian_det_eq_of_scale (N : Network S) (κ : N.RateConstants) (lam : ℝ)
    (hlam : 0 < lam) (x₀ : Concentration S) (y : Fin N.stoichRank → ℝ) :
    ((SignType.sign (N.reducedJacobian ⟨fun r => lam * κ.k r,
      fun r => mul_pos hlam (κ.positive r)⟩ x₀ y).det : SignType) : ℤ)
      = ((SignType.sign (N.reducedJacobian κ x₀ y).det : SignType) : ℤ) := by
  have hscale := reducedJacobian_det_scale N κ lam hlam x₀ y
  rw [hscale]
  rw [sign_mul, sign_pos (pow_pos hlam N.stoichRank)]
  rfl

/-- **The rank-one instance of the homogeneity: the reduced determinant is affine in the rate
constants.**  For a network of stoichiometric rank one the degree-`s` homogeneity reads
`det = lam * det`, i.e. the reduced determinant is an affine (indeed linear) function of the
rates.  This is the rank-one counterpart of `Network.reducedDerivOf_smul`
(`CRNT.Multistationarity.MultistationarityRegionDescription`), and the reason why the classical
single-product reading of the rank-one reduced determinant is impossible
(`Network.not_eq_rateProduct_mul`). -/
theorem reducedJacobian_det_scale_of_stoichRank_one (N : Network S) (κ : N.RateConstants)
    (lam : ℝ) (hlam : 0 < lam) (x₀ : Concentration S) (y : Fin N.stoichRank → ℝ)
    (hrank : N.stoichRank = 1) :
    (N.reducedJacobian ⟨fun r => lam * κ.k r, fun r => mul_pos hlam (κ.positive r)⟩ x₀ y).det
      = lam * (N.reducedJacobian κ x₀ y).det := by
  have hpow : lam ^ N.stoichRank = lam := by
    rw [hrank, pow_one]
  rw [reducedJacobian_det_scale N κ lam hlam x₀ y, hpow]

/-! ## 2. The sign rule for a Cauchy–Binet term -/

/-- **The cast of a product of two signs is the product of the casts.**  The sign type is
multiplicative when embedded in `ℤ`. -/
theorem signType_cast_mul (a b : SignType) :
    ((↑(a * b : SignType) : ℤ)) = (↑a : ℤ) * (↑b : ℤ) := by
  cases a <;> cases b <;> decide

/-- **The sign rule for a Cauchy–Binet term.**  The sign of
`det(circuit matrix) * (∏ κ_r) * det(gradient matrix)` is the product of the signs of the two
minors: the rate product is positive, so it contributes `+1`.

This is the sign rule of the higher-rank circuit reading of Conradi–Feliu–Mincheva–Wiuf
(Theorem 1): a Cauchy–Binet term is positive when the circuit minor and the gradient minor have
the same sign, negative when they have opposite signs, and vanishes when one of them vanishes. -/
theorem cauchyBinet_term_sign
    (N : Network S)
    (chart : (Fin N.stoichRank → ℝ) →L[ℝ] (S → ℝ))
    (proj : (S → ℝ) →L[ℝ] (Fin N.stoichRank → ℝ))
    (κ : N.R → ℝ) (x : Concentration S) (f : Fin N.stoichRank → N.R)
    (hκ : ∀ r, 0 < κ r) :
    ((SignType.sign ((circuitMatrix N proj f).det * (∏ j, κ (f j)) *
        (gradientMatrix N chart x f).det) : SignType) : ℤ)
      = ((SignType.sign (circuitMatrix N proj f).det : SignType) : ℤ) *
        ((SignType.sign (gradientMatrix N chart x f).det : SignType) : ℤ) := by
  have hP : 0 < ∏ j, κ (f j) := by
    refine Finset.prod_pos fun j _ => hκ (f j)
  have hsign : (SignType.sign ((circuitMatrix N proj f).det * (∏ j, κ (f j)) *
      (gradientMatrix N chart x f).det) : SignType)
      = (SignType.sign (circuitMatrix N proj f).det : SignType) *
        (SignType.sign (gradientMatrix N chart x f).det : SignType) := by
    rw [sign_mul, sign_mul, sign_pos hP]
    simp only [mul_one]
  rw [hsign]
  exact signType_cast_mul _ _

/-! ## 3. The converse characterisation of the non-vanishing terms -/

/-- **The converse characterisation of the non-vanishing Cauchy–Binet terms.**  A term of the
Cauchy–Binet expansion is nonzero exactly when the chart reaction vectors of the reactions of
the supporting subset are linearly independent; equivalently, the circuit matrix of the subset is
invertible.

This is the converse of `Network.circuitMatrix_det_eq_zero_of_dep` and
`Network.circuitMatrix_det_eq_zero_of_circuit`: the terms that *survive* in the expansion are
exactly those whose supporting subset carries **no** circuit.  (The framing "the non-vanishing
terms are exactly the circuits" is inverted; a circuit makes the minor *vanish*.) -/
theorem circuitMatrix_det_ne_zero_iff_chartVectors_linearIndependent
    (N : Network S) (proj : (S → ℝ) →L[ℝ] (Fin N.stoichRank → ℝ))
    (f : Fin N.stoichRank → N.R) :
    (circuitMatrix N proj f).det ≠ 0 ↔
      LinearIndependent ℝ (fun j => chartVector N proj (f j)) := by
  have hcol : (circuitMatrix N proj f).col = fun j => chartVector N proj (f j) := by
    funext j
    funext i
    rfl
  constructor
  · intro h
    have h1 : LinearIndependent ℝ (circuitMatrix N proj f).col :=
      Matrix.linearIndependent_cols_of_det_ne_zero h
    rw [hcol] at h1
    exact h1
  · intro hli
    rw [← hcol] at hli
    have hns : (circuitMatrix N proj f).Nonsingular :=
      Matrix.linearIndependent_col_iff.mp hli
    exact Matrix.nonsingular_iff_det_ne_zero.mp hns

/-- **The canonical chart is compatible with the projection on reaction vectors.**  The
chart–projection hypothesis `chart (proj (reactionVector r)) = reactionVector r` that the notes of
leaf M13 list for the converse characterisation of the non-vanishing terms is *automatic* for the
canonical chart: the reaction vector lies in the stoichiometric subspace, on which the chart is
the left inverse of the projection. -/
theorem stoichChart_stoichProj_reactionVector (N : Network S) (r : N.R) :
    N.stoichChart (N.stoichProj (N.reactionVector r)) = N.reactionVector r :=
  N.stoichChart_stoichProj (N.reactionVector_mem_stoichSubspace r)

/-! ## 4. The exceptional local degree is the sign of the Cauchy–Binet sum -/

/-- **The exceptional local degree is the sign of the Cauchy–Binet sum.**  The local degree of
the steady-state map at a steady state of the class is the sign of the reduced Jacobian
determinant there, and the reduced determinant *is* the Cauchy–Binet sum; hence the local degree
is `+1` exactly when the Cauchy–Binet sum is positive. -/
theorem localDegree_eq_one_iff_reducedDet_pos
    (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S) (y : Fin N.stoichRank → ℝ)
    (hzero : N.steadyStateMap κ x₀ y = 0)
    (hfin : (N.steadyStateMap κ x₀ ⁻¹' {0} ∩ {y}).Finite) :
    localDegreeOn (N.steadyStateMap κ x₀) 0 {y} hfin = 1 ↔
      0 < (N.reducedJacobian κ x₀ y).det := by
  rw [N.localDegreeOn_steadyStateMap_singleton_eq_sign_reducedDet κ x₀ y hzero hfin]
  constructor
  · intro h
    have hs : (SignType.sign (N.reducedJacobian κ x₀ y).det : SignType) = 1 := by
      rcases lt_trichotomy (N.reducedJacobian κ x₀ y).det 0 with hneg | hzero' | hpos
      · simp [sign_neg hneg] at h
      · simp [hzero', sign_zero] at h
      · exact sign_pos hpos
    rw [sign_eq_one_iff] at hs
    exact hs
  · intro h
    rw [sign_pos h]
    rfl

/-- **The exceptional local degree is the sign of the Cauchy–Binet sum, written out.**  The
local degree of the steady-state map at a steady state of the class is `+1` exactly when the
Cauchy–Binet expansion of the reduced determinant is positive.  This is the point where the
algebraic content of the Cauchy–Binet expansion meets the degree theory: the sign of the
Cauchy–Binet sum is the local degree of the steady-state map, hence a summand of the class
degree. -/
theorem localDegree_eq_one_iff_cauchyBinet_sum_pos
    (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S) (y : Fin N.stoichRank → ℝ)
    (hzero : N.steadyStateMap κ x₀ y = 0)
    (hfin : (N.steadyStateMap κ x₀ ⁻¹' {0} ∩ {y}).Finite) :
    localDegreeOn (N.steadyStateMap κ x₀) 0 {y} hfin = 1 ↔
      0 < (∑ S ∈ ((Finset.univ : Finset (Fin (Fintype.card N.R))).powersetCard N.stoichRank).attach,
        (circuitMatrix N N.stoichProj
          (subsetReactions N (Fintype.equivFin N.R) S.1
            (Finset.mem_powersetCard.mp S.2).2)).det
          * (∏ j, κ.k (subsetReactions N (Fintype.equivFin N.R) S.1
              (Finset.mem_powersetCard.mp S.2).2 j))
          * (gradientMatrix N N.stoichChart (N.affineChart x₀ y)
              (subsetReactions N (Fintype.equivFin N.R) S.1
                (Finset.mem_powersetCard.mp S.2).2)).det) := by
  rw [← reducedJacobian_det_eq_cauchyBinet N κ x₀ y]
  exact localDegree_eq_one_iff_reducedDet_pos N κ x₀ y hzero hfin

/-! ## 5. A concrete instance: the fully open two-species network -/

namespace DegreeExampleHomogeneity

open DegreeExample

/-- **The reduced determinant of the fully open two-species instance at its steady state is `1`.**
The network has stoichiometric rank `2`, so its reduced determinant is a *degree-two* object in
the rate constants. -/
theorem det_at_b : (N.reducedJacobian rates 0 b).det = 1 :=
  DegreeExampleCheck.reducedJacobian_det_at_b

/-- **Doubling all rate constants multiplies the reduced determinant by `2 ^ 2 = 4`.**  This is
the degree-`s` homogeneity at a concrete instance: the reduced determinant of the two-species
fully open network is `1` for unit rates and `4` for doubled rates. -/
theorem det_scale_two :
    (N.reducedJacobian ⟨fun r => 2 * rates.k r, fun r => mul_pos (by norm_num) (rates.positive r)⟩
      0 b).det = 4 := by
  rw [reducedJacobian_det_scale N rates 2 (by norm_num) 0 b]
  rw [det_at_b]
  norm_num [DegreeExample.stoichRank_eq]

end DegreeExampleHomogeneity

end Network

end CRNT

/-! ## Axioms -/

#print axioms CRNT.Network.reducedJacobianInChart_det_scale
#print axioms CRNT.Network.reducedJacobian_det_scale
#print axioms CRNT.Network.sign_reducedJacobian_det_eq_of_scale
#print axioms CRNT.Network.reducedJacobian_det_scale_of_stoichRank_one
#print axioms CRNT.Network.cauchyBinet_term_sign
#print axioms CRNT.Network.circuitMatrix_det_ne_zero_iff_chartVectors_linearIndependent
#print axioms CRNT.Network.stoichChart_stoichProj_reactionVector
#print axioms CRNT.Network.localDegree_eq_one_iff_reducedDet_pos
#print axioms CRNT.Network.localDegree_eq_one_iff_cauchyBinet_sum_pos
#print axioms CRNT.Network.DegreeExampleHomogeneity.det_at_b
#print axioms CRNT.Network.DegreeExampleHomogeneity.det_scale_two
