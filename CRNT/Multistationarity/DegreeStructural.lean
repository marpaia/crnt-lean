import CRNT.Multistationarity.DegreeExistence
import CRNT.Multistationarity.GaleNikaido
import CRNT.Multistationarity.MultistationarityRegion

/-!
# The degree of the steady-state map is the sign of the reduced Jacobian determinant

This module supplies the **structural criterion for a nonzero degree** that was the remaining
gap of field-map leaf **M9** ("Brouwer degree and steady-state existence", the
Conradi–Feliu–Mincheva–Wiuf degree argument in dimension `s ≥ 2`).

## The mathematical content

Fix a network `N`, positive rate constants `κ`, and a class representative `x₀`.  In the chart
coordinates of the compatibility class (`ClassCoord N = Fin N.stoichRank → ℝ`) the mass-action
field is the **reduced field**

`G = N.steadyStateMap κ x₀ = N.reducedField κ x₀ = stoichProj ∘ F ∘ affineChart`,

whose zeros are exactly the mass-action steady states of the class.  The relative Brouwer degree
of `G` on the nonnegative part of the class is `N.nonnegativeClassDegree` (a signed count over
`G ⁻¹' {0} ∩ N.nonnegativeClassRegion x₀`, each summand being `sign (det (DG x))` — see
`CRNT.Multistationarity.LocalDegreeOn`).

The **reduced Jacobian** `N.reducedJacobian κ x₀ y` is the matrix of the derivative of the
reduced field: `DG y = N.reducedJacobianCLM κ x₀ y` (`Network.reducedField_hasFDerivAt`), and its
determinant is the determinant of the mass-action Jacobian restricted to the stoichiometric
subspace, read in the chart (`Network.reducedJacobian_eq_mul`; the determinant is independent of
the chart).  Hence

```
sign (det (DG y)) = sign ((N.reducedJacobian κ x₀ y).det),
```

which is the bridge proved here as
`Network.det_fderiv_steadyStateMap_eq_reducedJacobian_det`.

Consequently:

* the **local degree** at a regular preimage `y₀` is the sign of the reduced determinant there
  (`Network.localDegreeOn_steadyStateMap_singleton_eq_sign_reducedDet`);
* the **class degree** is the sign of the reduced determinant at the (unique) preimage
  (`Network.nonnegativeClassDegree_eq_sign_reducedDet_of_unique_preimage`), hence `+1` when the
  reduced determinant is positive and `-1` when it is negative;
* a class with a unique steady state whose reduced determinant is **positive** therefore has a
  **nonzero class degree**, and (with the boundary non-vanishing hypothesis) a **positive steady
  state** in the class (`Network.exists_positiveSteadyState_of_positive_reducedDet`).

The last item is the classical "positive reduced determinant" criterion of
Conradi–Feliu–Mincheva–Wiuf, in the degree-theoretic form: the sign of the reduced determinant
at a steady state is what makes the degree nonzero.

## Conventions

* **Orientation.** The sign of a derivative determinant is read in the *chart* orientation of the
  class coordinates `Fin s → ℝ`, with `s = N.stoichRank`.  The local degree of a map at a
  regular preimage is `sign (det (Df))`, exactly as in `CRNT.localDegreeOn`; the degree of the
  identity is `+1` and the degree of `-id` in dimension `s` is `(-1)^s`
  (`CRNT.Network.DegreeExample.nonnegativeClassDegree_eq_one` computes `+1` for `s = 2`).
* **The reduced determinant is the reduced derivative in rank one.** For `s = 1` the reduced
  determinant *is* the derivative `φ'` of the scalar field along the class
  (`Network.reducedJacobian_det_eq_deriv`), and the class degree at a regular steady state is
  `sign φ'` (`Network.nonnegativeClassDegree_eq_sign_of_deriv_of_rank_one`).  This is the exact
  link to leaf **M13** ("Parameter regions for multistationarity"): the sign of `φ'` is the sign
  condition that separates uniqueness from multistationarity there
  (`Network.rankOne_multistationary_iff_det_pos`: the class is multistationary iff some positive
  steady state has a *positive* reduced determinant).  In the present module the same sign is the
  local degree of the steady-state map at that steady state: the multistationary signature
  `φ' > 0` is the signature "local degree `+1`", and the monostationary signature `φ' < 0` is the
  signature "local degree `-1`".
* **Sign convention of the published criterion.**  Conradi et al. write their determinant with
  the opposite sign in rank one (their determinant has the sign of `-φ'`, cf. the docstring of
  `CRNT.Multistationarity.RankOneParameterRegion`), so their sign `(-1)^{s+1}` is the
  "multistationary" signature.  The library's convention — the sign of `φ'`, i.e. of
  `Network.reducedJacobian`'s determinant — is the one used throughout this module, and it is the
  convention of `Network.rankOne_multistationary_iff_det_pos`.

## Relation to leaf M9

`CRNT.Multistationarity.DegreeExistence` provides the relative class degree, its existence
principle (`exists_positiveSteadyState_of_nonnegativeClassDegree_ne_zero`) and its
rate-constant independence (`nonnegativeClassDegree_rate_independent`).  What was missing is the
*structural* criterion for a nonzero degree: this module supplies it, in the form "the degree at a
steady state is the sign of the reduced Jacobian determinant there".

What is *not* supplied here: a general formula for the degree of the reduced field in terms of
the network structure (rate constants, SR-graph signs, toric volume), and the general
"positive determinant ⇒ *two* positive steady states" conclusion of Conradi et al. in dimension
`s ≥ 2`, which additionally needs the homotopy/degree argument on the perturbed map.  The
hypotheses carried here are the analytic ones of the degree machinery: finiteness of the zero set
inside the region (`hfin`), uniqueness of the preimage (`huniq`), and non-vanishing of the field
on the class boundary (`hbd`).  For classes with several steady states the "all reduced
determinants positive" variant is provided
(`Network.nonnegativeClassDegree_eq_card_of_reducedDet_pos`), but a class with *mixed* signs is
not covered by a general degree formula here.
-/

namespace CRNT

open scoped BigOperators Topology Classical

open Set Filter

/-! ## The local degree at a regular preimage -/

section LocalDegreeSign

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The relative degree on a one-point region.**  If `f y₀ = 0`, the relative degree of `f` at
`0` on the region `{y₀}` is the orientation sign of the derivative at `y₀`,
`sign (det (D f y₀))`.  This is the local degree of `f` at the regular preimage `y₀`. -/
theorem localDegreeOn_singleton (f : E → E) (y₀ : E) (hzero : f y₀ = 0)
    (hfin : (f ⁻¹' {(0 : E)} ∩ {y₀}).Finite) :
    localDegreeOn f 0 {y₀} hfin =
      ((SignType.sign (LinearMap.det (fderiv ℝ f y₀).toLinearMap) : SignType) : ℤ) := by
  have hmem : y₀ ∈ f ⁻¹' {(0 : E)} := by simp [hzero]
  have hset : f ⁻¹' {(0 : E)} ∩ {y₀} = {y₀} := by
    ext y
    constructor
    · intro hy
      have hy1 : f y = 0 := Set.mem_singleton_iff.mp hy.1
      have hy2 : y = y₀ := Set.mem_singleton_iff.mp hy.2
      exact Set.mem_singleton_iff.mpr hy2
    · intro hy
      have hy2 : y = y₀ := Set.mem_singleton_iff.mp hy
      subst hy2
      exact ⟨hmem, Set.mem_singleton_iff.mpr rfl⟩
  have htf : hfin.toFinset = {y₀} := by
    ext z
    rw [Set.Finite.mem_toFinset, hset, Finset.mem_singleton, Set.mem_singleton_iff]
  unfold localDegreeOn
  rw [htf, Finset.sum_singleton]

/-- **The relative degree with a unique preimage.**  If `y₀` is the only preimage of `0` and it
lies in the region `U`, the relative degree of `f` at `0` on `U` is the orientation sign of the
derivative at `y₀`, `sign (det (D f y₀))`.  This is the "the degree is the sum of the local
degrees over the preimages" principle in the case of a single preimage. -/
theorem localDegreeOn_eq_sign_det_of_unique_preimage (f : E → E) (y₀ : E) (hzero : f y₀ = 0)
    (huniq : ∀ y, f y = 0 → y = y₀) {U : Set E} (hy₀ : y₀ ∈ U)
    (hfin : (f ⁻¹' {(0 : E)} ∩ U).Finite) :
    localDegreeOn f 0 U hfin =
      ((SignType.sign (LinearMap.det (fderiv ℝ f y₀).toLinearMap) : SignType) : ℤ) := by
  have hmem : y₀ ∈ f ⁻¹' {(0 : E)} := by simp [hzero]
  have hset : f ⁻¹' {(0 : E)} ∩ U = {y₀} := by
    ext y
    constructor
    · intro hy
      have hy1 : f y = 0 := Set.mem_singleton_iff.mp hy.1
      have hy2 := huniq y hy1
      exact Set.mem_singleton_iff.mpr hy2
    · intro hy
      have hy2 : y = y₀ := Set.mem_singleton_iff.mp hy
      subst hy2
      exact ⟨hmem, hy₀⟩
  have htf : hfin.toFinset = {y₀} := by
    ext z
    rw [Set.Finite.mem_toFinset, hset, Finset.mem_singleton, Set.mem_singleton_iff]
  unfold localDegreeOn
  rw [htf, Finset.sum_singleton]

/-- **The local degree at a regular preimage is `±1`.**  At a point where the derivative
determinant is nonzero, the orientation sign is `+1` or `-1`. -/
theorem localDegreeOn_singleton_eq_one_or_neg_one (f : E → E) (y₀ : E) (hzero : f y₀ = 0)
    (hfin : (f ⁻¹' {(0 : E)} ∩ {y₀}).Finite)
    (hdet : LinearMap.det (fderiv ℝ f y₀).toLinearMap ≠ 0) :
    localDegreeOn f 0 {y₀} hfin = 1 ∨ localDegreeOn f 0 {y₀} hfin = -1 := by
  rw [localDegreeOn_singleton f y₀ hzero hfin]
  rcases lt_trichotomy (LinearMap.det (fderiv ℝ f y₀).toLinearMap) 0 with h | h | h
  · refine Or.inr ?_
    rw [sign_neg h]
    rfl
  · exact absurd h hdet
  · refine Or.inl ?_
    rw [sign_pos h]
    rfl

end LocalDegreeSign

namespace Network

open scoped BigOperators Topology Classical

open Set Filter

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ## The reduced Jacobian is the derivative of the reduced field -/

/-- **The derivative of the steady-state map is the reduced Jacobian operator.**  The reduced
field `N.reducedField κ x₀` differentiates to `N.reducedJacobianCLM κ x₀ y`
(`Network.reducedField_hasFDerivAt`), and the steady-state map *is* the reduced field
(`Network.steadyStateMap`). -/
theorem fderiv_steadyStateMap (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S)
    (y : ClassCoord N) :
    fderiv ℝ (N.steadyStateMap κ x₀) y = N.reducedJacobianCLM κ x₀ y := by
  have h : HasFDerivAt (N.steadyStateMap κ x₀) (N.reducedJacobianCLM κ x₀ y) y := by
    simpa only [Network.steadyStateMap] using N.reducedField_hasFDerivAt κ x₀ y
  exact h.fderiv

/-- **The determinant of the derivative of the steady-state map is the determinant of the
reduced Jacobian.**  This is the bridge between the degree machinery (which reads
`det (D (steadyStateMap))`) and the reduced Jacobian (the matrix of the mass-action Jacobian
restricted to the stoichiometric subspace, read in the chart). -/
theorem det_fderiv_steadyStateMap_eq_reducedJacobian_det (N : Network S) (κ : N.RateConstants)
    (x₀ : Concentration S) (y : ClassCoord N) :
    LinearMap.det (fderiv ℝ (N.steadyStateMap κ x₀) y).toLinearMap
      = (N.reducedJacobian κ x₀ y).det := by
  rw [fderiv_steadyStateMap N κ x₀ y]
  have h1 : LinearMap.det (N.reducedJacobianCLM κ x₀ y).toLinearMap
      = (jacobianMatrix (N.reducedJacobianCLM κ x₀ y)).det := by
    rw [jacobianMatrix_det]
  rw [h1, N.jacobianMatrix_reducedField]

/-! ## The local degree of the steady-state map -/

/-- **The local degree of the steady-state map at a regular preimage is the sign of the reduced
Jacobian determinant.**  At a preimage `y₀` of `0`, the relative degree on the one-point region
`{y₀}` is `sign (det (D (steadyStateMap) y₀))`, which by
`Network.det_fderiv_steadyStateMap_eq_reducedJacobian_det` is the sign of the reduced Jacobian
determinant `Network.reducedJacobian κ x₀ y₀`.  A positive reduced determinant therefore gives the
local degree `+1`, a negative one the local degree `-1`. -/
theorem localDegreeOn_steadyStateMap_singleton_eq_sign_reducedDet
    (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S) (y₀ : ClassCoord N)
    (hzero : N.steadyStateMap κ x₀ y₀ = 0)
    (hfin : (N.steadyStateMap κ x₀ ⁻¹' {0} ∩ {y₀}).Finite) :
    localDegreeOn (N.steadyStateMap κ x₀) 0 {y₀} hfin =
      ((SignType.sign (N.reducedJacobian κ x₀ y₀).det : SignType) : ℤ) := by
  rw [localDegreeOn_singleton (N.steadyStateMap κ x₀) y₀ hzero hfin]
  rw [N.det_fderiv_steadyStateMap_eq_reducedJacobian_det]

/-- **The local degree of the steady-state map at a regular preimage is `±1`.**  The reduced
Jacobian at `y₀` is invertible, so its determinant is nonzero and the local degree is `+1` or
`-1`. -/
theorem localDegreeOn_steadyStateMap_singleton_eq_one_or_neg_one
    (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S) (y₀ : ClassCoord N)
    (hzero : N.steadyStateMap κ x₀ y₀ = 0)
    (hfin : (N.steadyStateMap κ x₀ ⁻¹' {0} ∩ {y₀}).Finite)
    (hdet : (N.reducedJacobian κ x₀ y₀).det ≠ 0) :
    localDegreeOn (N.steadyStateMap κ x₀) 0 {y₀} hfin = 1 ∨
      localDegreeOn (N.steadyStateMap κ x₀) 0 {y₀} hfin = -1 := by
  rw [N.localDegreeOn_steadyStateMap_singleton_eq_sign_reducedDet κ x₀ y₀ hzero hfin]
  rcases lt_trichotomy ((N.reducedJacobian κ x₀ y₀).det) 0 with h | h | h
  · refine Or.inr ?_
    rw [sign_neg h]
    rfl
  · exact absurd h hdet
  · refine Or.inl ?_
    rw [sign_pos h]
    rfl

/-- **The relative degree of the steady-state map on a region with a unique preimage is the sign
of the reduced Jacobian determinant at that preimage.** -/
theorem localDegreeOn_steadyStateMap_eq_sign_reducedDet_of_unique_preimage
    (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S) (y₀ : ClassCoord N)
    (hzero : N.steadyStateMap κ x₀ y₀ = 0)
    (huniq : ∀ y, N.steadyStateMap κ x₀ y = 0 → y = y₀)
    {U : Set (ClassCoord N)} (hy₀ : y₀ ∈ U)
    (hfin : (N.steadyStateMap κ x₀ ⁻¹' {0} ∩ U).Finite) :
    localDegreeOn (N.steadyStateMap κ x₀) 0 U hfin =
      ((SignType.sign (N.reducedJacobian κ x₀ y₀).det : SignType) : ℤ) := by
  rw [localDegreeOn_eq_sign_det_of_unique_preimage (N.steadyStateMap κ x₀) y₀ hzero huniq hy₀ hfin]
  rw [N.det_fderiv_steadyStateMap_eq_reducedJacobian_det]

/-! ## The class degree is the sign of the reduced Jacobian determinant -/

/-- **The class degree is the sign of the reduced Jacobian determinant at the unique steady
state of the class.**  This is the structural criterion for a nonzero degree: the sign of the
reduced determinant at the (unique) steady state of the nonnegative class determines the class
degree.  In particular a positive reduced determinant gives the degree `+1` and a negative one
the degree `-1`. -/
theorem nonnegativeClassDegree_eq_sign_reducedDet_of_unique_preimage
    (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S) (y₀ : ClassCoord N)
    (hzero : N.steadyStateMap κ x₀ y₀ = 0)
    (hy₀ : y₀ ∈ N.nonnegativeClassRegion x₀)
    (huniq : ∀ y, N.steadyStateMap κ x₀ y = 0 → y = y₀)
    (hfin : (N.steadyStateMap κ x₀ ⁻¹' {0} ∩ N.nonnegativeClassRegion x₀).Finite) :
    N.nonnegativeClassDegree κ x₀ hfin =
      ((SignType.sign (N.reducedJacobian κ x₀ y₀).det : SignType) : ℤ) := by
  unfold nonnegativeClassDegree
  rw [N.localDegreeOn_steadyStateMap_eq_sign_reducedDet_of_unique_preimage κ x₀ y₀
    hzero huniq hy₀ hfin]

/-- **The degree on the positive part of the class is the sign of the reduced Jacobian
determinant at the unique steady state of the class.** -/
theorem positiveClassDegree_eq_sign_reducedDet_of_unique_preimage
    (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S) (y₀ : ClassCoord N)
    (hzero : N.steadyStateMap κ x₀ y₀ = 0)
    (hy₀ : y₀ ∈ N.positiveClassRegion x₀)
    (huniq : ∀ y, N.steadyStateMap κ x₀ y = 0 → y = y₀)
    (hfin : (N.steadyStateMap κ x₀ ⁻¹' {0} ∩ N.positiveClassRegion x₀).Finite) :
    N.positiveClassDegree κ x₀ hfin =
      ((SignType.sign (N.reducedJacobian κ x₀ y₀).det : SignType) : ℤ) := by
  unfold positiveClassDegree
  rw [N.localDegreeOn_steadyStateMap_eq_sign_reducedDet_of_unique_preimage κ x₀ y₀
    hzero huniq hy₀ hfin]

/-- **A positive reduced determinant at the unique steady state gives the class degree `+1`.**
This is the structural criterion for a *nonzero* degree: a class with a unique steady state whose
reduced Jacobian determinant is positive has degree `+1`. -/
theorem nonnegativeClassDegree_eq_one_of_unique_preimage_of_det_pos
    (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S) (y₀ : ClassCoord N)
    (hzero : N.steadyStateMap κ x₀ y₀ = 0)
    (hy₀ : y₀ ∈ N.nonnegativeClassRegion x₀)
    (huniq : ∀ y, N.steadyStateMap κ x₀ y = 0 → y = y₀)
    (hfin : (N.steadyStateMap κ x₀ ⁻¹' {0} ∩ N.nonnegativeClassRegion x₀).Finite)
    (hdet : 0 < (N.reducedJacobian κ x₀ y₀).det) :
    N.nonnegativeClassDegree κ x₀ hfin = 1 := by
  rw [N.nonnegativeClassDegree_eq_sign_reducedDet_of_unique_preimage κ x₀ y₀ hzero hy₀ huniq hfin]
  rw [sign_pos hdet]
  rfl

/-- **A negative reduced determinant at the unique steady state gives the class degree `-1`.** -/
theorem nonnegativeClassDegree_eq_neg_one_of_unique_preimage_of_det_neg
    (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S) (y₀ : ClassCoord N)
    (hzero : N.steadyStateMap κ x₀ y₀ = 0)
    (hy₀ : y₀ ∈ N.nonnegativeClassRegion x₀)
    (huniq : ∀ y, N.steadyStateMap κ x₀ y = 0 → y = y₀)
    (hfin : (N.steadyStateMap κ x₀ ⁻¹' {0} ∩ N.nonnegativeClassRegion x₀).Finite)
    (hdet : (N.reducedJacobian κ x₀ y₀).det < 0) :
    N.nonnegativeClassDegree κ x₀ hfin = -1 := by
  rw [N.nonnegativeClassDegree_eq_sign_reducedDet_of_unique_preimage κ x₀ y₀ hzero hy₀ huniq hfin]
  rw [sign_neg hdet]
  rfl

/-- **A nonzero reduced determinant at the unique steady state gives a nonzero class degree.**
Equivalently: the unique steady state of the class is *regular* (the reduced Jacobian is
invertible) exactly when the class degree is nonzero. -/
theorem nonnegativeClassDegree_ne_zero_of_unique_preimage_of_det_ne_zero
    (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S) (y₀ : ClassCoord N)
    (hzero : N.steadyStateMap κ x₀ y₀ = 0)
    (hy₀ : y₀ ∈ N.nonnegativeClassRegion x₀)
    (huniq : ∀ y, N.steadyStateMap κ x₀ y = 0 → y = y₀)
    (hfin : (N.steadyStateMap κ x₀ ⁻¹' {0} ∩ N.nonnegativeClassRegion x₀).Finite)
    (hdet : (N.reducedJacobian κ x₀ y₀).det ≠ 0) :
    N.nonnegativeClassDegree κ x₀ hfin ≠ 0 := by
  rw [N.nonnegativeClassDegree_eq_sign_reducedDet_of_unique_preimage κ x₀ y₀ hzero hy₀ huniq hfin]
  exact sign_cast_ne_zero_of_ne_zero hdet

/-- **The class degree is nonzero exactly when the unique steady state of the class is
regular.**  This is the crispest form of the structural criterion: for a class with a unique
steady state, the class degree vanishes precisely when the reduced Jacobian determinant at that
steady state vanishes, i.e. precisely when the steady state is degenerate. -/
theorem nonnegativeClassDegree_ne_zero_iff_reducedDet_ne_zero_of_unique_preimage
    (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S) (y₀ : ClassCoord N)
    (hzero : N.steadyStateMap κ x₀ y₀ = 0)
    (hy₀ : y₀ ∈ N.nonnegativeClassRegion x₀)
    (huniq : ∀ y, N.steadyStateMap κ x₀ y = 0 → y = y₀)
    (hfin : (N.steadyStateMap κ x₀ ⁻¹' {0} ∩ N.nonnegativeClassRegion x₀).Finite) :
    N.nonnegativeClassDegree κ x₀ hfin ≠ 0 ↔ (N.reducedJacobian κ x₀ y₀).det ≠ 0 := by
  constructor
  · intro h hd
    have hz : ((SignType.sign (N.reducedJacobian κ x₀ y₀).det : SignType) : ℤ) = 0 := by
      simp [hd]
    rw [N.nonnegativeClassDegree_eq_sign_reducedDet_of_unique_preimage κ x₀ y₀ hzero hy₀ huniq hfin]
      at h
    exact h hz
  · exact N.nonnegativeClassDegree_ne_zero_of_unique_preimage_of_det_ne_zero κ x₀ y₀ hzero hy₀
      huniq hfin

/-- **The positive-region degree is `+1` at a unique steady state with positive reduced
determinant.** -/
theorem positiveClassDegree_eq_one_of_unique_preimage_of_det_pos
    (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S) (y₀ : ClassCoord N)
    (hzero : N.steadyStateMap κ x₀ y₀ = 0)
    (hy₀ : y₀ ∈ N.positiveClassRegion x₀)
    (huniq : ∀ y, N.steadyStateMap κ x₀ y = 0 → y = y₀)
    (hfin : (N.steadyStateMap κ x₀ ⁻¹' {0} ∩ N.positiveClassRegion x₀).Finite)
    (hdet : 0 < (N.reducedJacobian κ x₀ y₀).det) :
    N.positiveClassDegree κ x₀ hfin = 1 := by
  rw [N.positiveClassDegree_eq_sign_reducedDet_of_unique_preimage κ x₀ y₀ hzero hy₀ huniq hfin]
  rw [sign_pos hdet]
  rfl

/-! ## The "class degree" phrasing of the same statements -/

/-- **The class degree is the sign of the reduced Jacobian determinant at the unique preimage.**
This is `Network.nonnegativeClassDegree_eq_sign_reducedDet_of_unique_preimage`, phrased with the
name "class degree" for `Network.nonnegativeClassDegree`. -/
theorem classDegree_eq_sign_of_unique_preimage
    (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S) (y₀ : ClassCoord N)
    (hzero : N.steadyStateMap κ x₀ y₀ = 0)
    (hy₀ : y₀ ∈ N.nonnegativeClassRegion x₀)
    (huniq : ∀ y, N.steadyStateMap κ x₀ y = 0 → y = y₀)
    (hfin : (N.steadyStateMap κ x₀ ⁻¹' {0} ∩ N.nonnegativeClassRegion x₀).Finite) :
    N.nonnegativeClassDegree κ x₀ hfin =
      ((SignType.sign (N.reducedJacobian κ x₀ y₀).det : SignType) : ℤ) :=
  N.nonnegativeClassDegree_eq_sign_reducedDet_of_unique_preimage κ x₀ y₀ hzero hy₀ huniq hfin

/-- **A positive reduced determinant at the unique preimage gives the class degree `+1`.** -/
theorem classDegree_eq_one_of_unique_preimage_of_det_pos
    (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S) (y₀ : ClassCoord N)
    (hzero : N.steadyStateMap κ x₀ y₀ = 0)
    (hy₀ : y₀ ∈ N.nonnegativeClassRegion x₀)
    (huniq : ∀ y, N.steadyStateMap κ x₀ y = 0 → y = y₀)
    (hfin : (N.steadyStateMap κ x₀ ⁻¹' {0} ∩ N.nonnegativeClassRegion x₀).Finite)
    (hdet : 0 < (N.reducedJacobian κ x₀ y₀).det) :
    N.nonnegativeClassDegree κ x₀ hfin = 1 :=
  N.nonnegativeClassDegree_eq_one_of_unique_preimage_of_det_pos κ x₀ y₀ hzero hy₀ huniq hfin hdet

/-- **A negative reduced determinant at the unique preimage gives the class degree `-1`.** -/
theorem classDegree_eq_neg_one_of_unique_preimage_of_det_neg
    (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S) (y₀ : ClassCoord N)
    (hzero : N.steadyStateMap κ x₀ y₀ = 0)
    (hy₀ : y₀ ∈ N.nonnegativeClassRegion x₀)
    (huniq : ∀ y, N.steadyStateMap κ x₀ y = 0 → y = y₀)
    (hfin : (N.steadyStateMap κ x₀ ⁻¹' {0} ∩ N.nonnegativeClassRegion x₀).Finite)
    (hdet : (N.reducedJacobian κ x₀ y₀).det < 0) :
    N.nonnegativeClassDegree κ x₀ hfin = -1 :=
  N.nonnegativeClassDegree_eq_neg_one_of_unique_preimage_of_det_neg κ x₀ y₀ hzero hy₀ huniq hfin hdet

/-- **A nonzero reduced determinant at the unique preimage gives a nonzero class degree.** -/
theorem classDegree_ne_zero_of_unique_preimage_of_det_ne_zero
    (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S) (y₀ : ClassCoord N)
    (hzero : N.steadyStateMap κ x₀ y₀ = 0)
    (hy₀ : y₀ ∈ N.nonnegativeClassRegion x₀)
    (huniq : ∀ y, N.steadyStateMap κ x₀ y = 0 → y = y₀)
    (hfin : (N.steadyStateMap κ x₀ ⁻¹' {0} ∩ N.nonnegativeClassRegion x₀).Finite)
    (hdet : (N.reducedJacobian κ x₀ y₀).det ≠ 0) :
    N.nonnegativeClassDegree κ x₀ hfin ≠ 0 :=
  N.nonnegativeClassDegree_ne_zero_of_unique_preimage_of_det_ne_zero κ x₀ y₀ hzero hy₀ huniq hfin hdet

/-! ## The structural existence criterion -/

/-- **A positive reduced determinant at a steady state gives a positive steady state in the
class.**  This is the degree-theoretic form of the Conradi–Feliu–Mincheva–Wiuf "positive
determinant" criterion.

The reusable content is the *degree computation*: the unique steady state `y₀` of the class
contributes the local degree `sign (det (reducedJacobian at y₀))` to the class degree, so a
positive reduced determinant makes the class degree `+1`, hence nonzero
(`Network.classDegree_eq_one_of_unique_preimage_of_det_pos`).  The existence principle of
`CRNT.Multistationarity.DegreeExistence` then produces a zero of the steady-state map in the
nonnegative class, and the non-vanishing of the field on the class boundary (`hbd`) makes that
zero strictly positive.

Note that the hypotheses `hzero`, `hy₀` and `hbd` already force `y₀` itself to be a positive class
point (`nonnegativeClassRegion = positiveClassRegion ∪ classBoundary`, and the field does not
vanish on the boundary); the theorem is nevertheless proved through the degree machinery, which
is what makes the criterion reusable for classes with several steady states. -/
theorem exists_positiveSteadyState_of_positive_reducedDet
    (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S) (y₀ : ClassCoord N)
    (hzero : N.steadyStateMap κ x₀ y₀ = 0)
    (hy₀ : y₀ ∈ N.nonnegativeClassRegion x₀)
    (huniq : ∀ y, N.steadyStateMap κ x₀ y = 0 → y = y₀)
    (hfin : (N.steadyStateMap κ x₀ ⁻¹' {0} ∩ N.nonnegativeClassRegion x₀).Finite)
    (hdet : 0 < (N.reducedJacobian κ x₀ y₀).det)
    (hbd : ∀ y ∈ N.classBoundary x₀, N.steadyStateMap κ x₀ y ≠ 0) :
    ∃ x : Concentration S,
      N.StoichCompatible x₀ x ∧ Concentration.Positive x ∧ N.IsMassActionSteadyState κ x := by
  have hdeg : N.nonnegativeClassDegree κ x₀ hfin = 1 :=
    N.nonnegativeClassDegree_eq_one_of_unique_preimage_of_det_pos κ x₀ y₀ hzero hy₀ huniq hfin hdet
  exact N.exists_positiveSteadyState_of_nonnegativeClassDegree_ne_zero κ x₀ hfin
    (by rw [hdeg]; norm_num) hbd

/-- **A negative reduced determinant at a steady state also gives a positive steady state in the
class.**  The sign of the reduced determinant decides the *value* of the degree (`+1` or `-1`),
but either way the degree is nonzero, and the boundary non-vanishing turns it into a positive
steady state.  This is the counterpart of
`Network.exists_positiveSteadyState_of_positive_reducedDet`: for the degree argument only the
*nonvanishing* of the reduced determinant at the steady state matters, while its *sign* fixes the
value of the degree. -/
theorem exists_positiveSteadyState_of_negative_reducedDet
    (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S) (y₀ : ClassCoord N)
    (hzero : N.steadyStateMap κ x₀ y₀ = 0)
    (hy₀ : y₀ ∈ N.nonnegativeClassRegion x₀)
    (huniq : ∀ y, N.steadyStateMap κ x₀ y = 0 → y = y₀)
    (hfin : (N.steadyStateMap κ x₀ ⁻¹' {0} ∩ N.nonnegativeClassRegion x₀).Finite)
    (hdet : (N.reducedJacobian κ x₀ y₀).det < 0)
    (hbd : ∀ y ∈ N.classBoundary x₀, N.steadyStateMap κ x₀ y ≠ 0) :
    ∃ x : Concentration S,
      N.StoichCompatible x₀ x ∧ Concentration.Positive x ∧ N.IsMassActionSteadyState κ x := by
  have hdeg : N.nonnegativeClassDegree κ x₀ hfin = -1 :=
    N.nonnegativeClassDegree_eq_neg_one_of_unique_preimage_of_det_neg κ x₀ y₀ hzero hy₀ huniq hfin hdet
  exact N.exists_positiveSteadyState_of_nonnegativeClassDegree_ne_zero κ x₀ hfin
    (by rw [hdeg]; norm_num) hbd

/-- **The class degree is nonzero whenever the unique steady state is regular.**  A steady state
is regular when the reduced Jacobian there is invertible, i.e. when its determinant is nonzero. -/
theorem exists_positiveSteadyState_of_regular_unique_steadyState
    (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S) (y₀ : ClassCoord N)
    (hzero : N.steadyStateMap κ x₀ y₀ = 0)
    (hy₀ : y₀ ∈ N.nonnegativeClassRegion x₀)
    (huniq : ∀ y, N.steadyStateMap κ x₀ y = 0 → y = y₀)
    (hfin : (N.steadyStateMap κ x₀ ⁻¹' {0} ∩ N.nonnegativeClassRegion x₀).Finite)
    (hdet : (N.reducedJacobian κ x₀ y₀).det ≠ 0)
    (hbd : ∀ y ∈ N.classBoundary x₀, N.steadyStateMap κ x₀ y ≠ 0) :
    ∃ x : Concentration S,
      N.StoichCompatible x₀ x ∧ Concentration.Positive x ∧ N.IsMassActionSteadyState κ x := by
  have hdeg : N.nonnegativeClassDegree κ x₀ hfin ≠ 0 :=
    N.nonnegativeClassDegree_ne_zero_of_unique_preimage_of_det_ne_zero κ x₀ y₀ hzero hy₀ huniq
      hfin hdet
  exact N.exists_positiveSteadyState_of_nonnegativeClassDegree_ne_zero κ x₀ hfin hdeg hbd

/-! ## The general "all reduced determinants positive" criterion -/

/-- **The class degree counts the steady states when all reduced determinants are positive.**
If every zero of the steady-state map in the nonnegative class has a *positive* reduced Jacobian
determinant, then every summand of the relative degree is `+1`, and the degree is the number of
those zeros.  This is the structural criterion for a nonzero degree without the uniqueness
hypothesis: the degree is positive as soon as there is one such steady state. -/
theorem nonnegativeClassDegree_eq_card_of_reducedDet_pos
    (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S)
    (hfin : (N.steadyStateMap κ x₀ ⁻¹' {0} ∩ N.nonnegativeClassRegion x₀).Finite)
    (hpos : ∀ x ∈ (N.steadyStateMap κ x₀ ⁻¹' {0} ∩ N.nonnegativeClassRegion x₀),
      0 < (N.reducedJacobian κ x₀ x).det) :
    N.nonnegativeClassDegree κ x₀ hfin = ((hfin.toFinset.card : ℕ) : ℤ) := by
  unfold nonnegativeClassDegree localDegreeOn
  rw [Finset.sum_congr rfl (fun x hx => ?_)]
  · rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  · rw [Set.Finite.mem_toFinset] at hx
    have hx0 : N.steadyStateMap κ x₀ x = 0 := Set.mem_singleton_iff.mp hx.1
    have hxdet : 0 < LinearMap.det (fderiv ℝ (N.steadyStateMap κ x₀) x).toLinearMap := by
      rw [N.det_fderiv_steadyStateMap_eq_reducedJacobian_det]
      exact hpos x ⟨hx0, hx.2⟩
    rw [sign_pos hxdet]
    rfl

/-- **A positive class degree from positive reduced determinants.**  Under the hypotheses of
`nonnegativeClassDegree_eq_card_of_reducedDet_pos`, the class degree is positive as soon as the
zero set in the nonnegative class is nonempty. -/
theorem nonnegativeClassDegree_pos_of_reducedDet_pos
    (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S)
    (hfin : (N.steadyStateMap κ x₀ ⁻¹' {0} ∩ N.nonnegativeClassRegion x₀).Finite)
    (hpos : ∀ x ∈ (N.steadyStateMap κ x₀ ⁻¹' {0} ∩ N.nonnegativeClassRegion x₀),
      0 < (N.reducedJacobian κ x₀ x).det)
    (hex : (N.steadyStateMap κ x₀ ⁻¹' {0} ∩ N.nonnegativeClassRegion x₀).Nonempty) :
    0 < N.nonnegativeClassDegree κ x₀ hfin := by
  rw [N.nonnegativeClassDegree_eq_card_of_reducedDet_pos κ x₀ hfin hpos]
  have hne : hfin.toFinset.Nonempty := (Set.Finite.toFinset_nonempty hfin).mpr hex
  have hcard : 0 < hfin.toFinset.card := Finset.card_pos.mpr hne
  exact_mod_cast hcard

/-- **A positive steady state from positive reduced determinants.**  If the steady-state map has
a zero in the nonnegative class at which the reduced Jacobian determinant is positive, and all its
zeros in the nonnegative class have positive reduced determinant, then the class degree is
positive, hence nonzero, and (with the boundary non-vanishing) the class carries a positive
steady state. -/
theorem exists_positiveSteadyState_of_reducedDet_pos
    (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S)
    (hfin : (N.steadyStateMap κ x₀ ⁻¹' {0} ∩ N.nonnegativeClassRegion x₀).Finite)
    (hpos : ∀ x ∈ (N.steadyStateMap κ x₀ ⁻¹' {0} ∩ N.nonnegativeClassRegion x₀),
      0 < (N.reducedJacobian κ x₀ x).det)
    (hex : ∃ x ∈ N.nonnegativeClassRegion x₀, N.steadyStateMap κ x₀ x = 0)
    (hbd : ∀ y ∈ N.classBoundary x₀, N.steadyStateMap κ x₀ y ≠ 0) :
    ∃ x : Concentration S,
      N.StoichCompatible x₀ x ∧ Concentration.Positive x ∧ N.IsMassActionSteadyState κ x := by
  have hnonempty : (N.steadyStateMap κ x₀ ⁻¹' {0} ∩ N.nonnegativeClassRegion x₀).Nonempty := by
    obtain ⟨x, hxmem, hxz⟩ := hex
    exact ⟨x, ⟨hxz, hxmem⟩⟩
  have hdeg : 0 < N.nonnegativeClassDegree κ x₀ hfin :=
    N.nonnegativeClassDegree_pos_of_reducedDet_pos κ x₀ hfin hpos hnonempty
  exact N.exists_positiveSteadyState_of_nonnegativeClassDegree_ne_zero κ x₀ hfin hdeg.ne' hbd

/-! ## Regularity of the reduced Jacobian -/

/-- **The reduced Jacobian at a class point is invertible exactly when its determinant is
nonzero.**  A steady state is *regular* in the sense of the Conradi–Feliu–Mincheva–Wiuf
nondegeneracy hypothesis when the reduced Jacobian there is invertible. -/
theorem exists_reducedJacobianCLM_equiv_of_det_ne_zero
    (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S) (y : ClassCoord N)
    (hdet : (N.reducedJacobian κ x₀ y).det ≠ 0) :
    ∃ e : (Fin N.stoichRank → ℝ) ≃L[ℝ] (Fin N.stoichRank → ℝ),
      (e : (Fin N.stoichRank → ℝ) →L[ℝ] (Fin N.stoichRank → ℝ)) = N.reducedJacobianCLM κ x₀ y := by
  have hdet' : (N.reducedJacobianCLM κ x₀ y).det ≠ 0 := by
    rw [← jacobianMatrix_det, N.jacobianMatrix_reducedField]
    exact hdet
  exact ⟨(N.reducedJacobianCLM κ x₀ y).toContinuousLinearEquivOfDetNeZero hdet', rfl⟩

/-! ## Rank one: the degree is the sign of the reduced derivative -/

/-- **In rank one the class degree is the sign of the reduced derivative `φ'`.**  For a
rank-one network the reduced determinant *is* the derivative of the scalar field along the class
(`Network.reducedJacobian_det_eq_deriv`), so the local degree of the steady-state map at a steady
state of the class is `sign φ'`.  This is the precise link to leaf **M13**: `φ' > 0` is the
multistationary signature of Conradi–Feliu–Mincheva–Wiuf (as in
`Network.rankOne_multistationary_iff_det_pos`), and it is exactly the signature "local degree
`+1`"; `φ' < 0` is the monostationary signature and the signature "local degree `-1`". -/
theorem nonnegativeClassDegree_eq_sign_of_deriv_of_rank_one
    (N : Network S) (κ : N.RateConstants) (hcard : N.stoichRank = 1)
    {v : Concentration S} (hspan : N.stoichSubspace = Submodule.span ℝ {v})
    {i₀ : S} (hi₀ : v i₀ ≠ 0) (x₀ : Concentration S) (t : ℝ)
    (hzero : N.steadyStateMap κ x₀ (N.chartCoord x₀ (x₀ + t • v)) = 0)
    (hy₀ : N.chartCoord x₀ (x₀ + t • v) ∈ N.nonnegativeClassRegion x₀)
    (huniq : ∀ y, N.steadyStateMap κ x₀ y = 0 → y = N.chartCoord x₀ (x₀ + t • v))
    (hfin : (N.steadyStateMap κ x₀ ⁻¹' {0} ∩ N.nonnegativeClassRegion x₀).Finite) :
    N.nonnegativeClassDegree κ x₀ hfin =
      ((SignType.sign (deriv (N.lineField κ x₀ v i₀) t) : SignType) : ℤ) := by
  rw [N.nonnegativeClassDegree_eq_sign_reducedDet_of_unique_preimage κ x₀
    (N.chartCoord x₀ (x₀ + t • v)) hzero hy₀ huniq hfin]
  rw [N.reducedJacobian_det_eq_deriv κ hcard hspan hi₀ x₀ t]

/-! ## A consistency check on the concrete two-species instance -/

namespace DegreeExampleCheck

open DegreeExample

/-- **The reduced Jacobian determinant at the unique steady state of the two-species example is
`1`.**  The reduced field of that network is the affine map `y ↦ b - y`, whose derivative at `b`
is `-id`; in dimension `2` the determinant of `-id` is `1`
(`DegreeExample.det_neg_id_classCoord`).  The reduced Jacobian has the same determinant, by
`Network.det_fderiv_steadyStateMap_eq_reducedJacobian_det`.  This is the consistency check
between the new structural criterion and the class degree computed earlier by a different route
(`DegreeExample.nonnegativeClassDegree_eq_one`). -/
theorem reducedJacobian_det_at_b :
    (N.reducedJacobian rates 0 b).det = 1 := by
  have hderiv : fderiv ℝ (N.steadyStateMap rates 0) b
      = -(ContinuousLinearMap.id ℝ (ClassCoord N)) := by
    have hfun : N.steadyStateMap rates 0 = fun y : ClassCoord N => b - y := funext steadyStateMap_eq
    rw [hfun]
    simpa using (fderiv_const_sub (𝕜 := ℝ) (x := b) (c := b) (f := id))
  rw [← N.det_fderiv_steadyStateMap_eq_reducedJacobian_det]
  rw [hderiv]
  exact det_neg_id_classCoord

/-- **The unique steady state of the two-species example is a regular one.** -/
theorem reducedJacobian_det_at_b_pos : 0 < (N.reducedJacobian rates 0 b).det := by
  rw [reducedJacobian_det_at_b]
  norm_num

/-- **The class degree of the two-species example is `+1` by the structural criterion.**  This
rederives `DegreeExample.nonnegativeClassDegree_eq_one` through the new criterion: the class has
a unique steady state, and the reduced Jacobian determinant there is positive, so the class degree
is `+1`. -/
theorem classDegree_eq_one :
    N.nonnegativeClassDegree rates 0 hfinN = 1 := by
  refine N.classDegree_eq_one_of_unique_preimage_of_det_pos rates 0 b ?_ ?_ ?_ hfinN ?_
  · rw [steadyStateMap_eq]
    simp
  · exact b_mem_nonnegative
  · intro y hy
    rw [steadyStateMap_eq] at hy
    exact (sub_eq_zero.mp hy).symm
  · exact reducedJacobian_det_at_b_pos

/-- **The two-species example has a positive steady state, by the structural criterion.**  The
existence is now obtained from the sign of the reduced Jacobian determinant at the unique steady
state, rather than from the class degree computed by hand. -/
theorem exists_positive_steady_state :
    ∃ x : Concentration (Fin 2),
      N.StoichCompatible 0 x ∧ Concentration.Positive x ∧ N.IsMassActionSteadyState rates x :=
  N.exists_positiveSteadyState_of_positive_reducedDet rates 0 b
    (by rw [steadyStateMap_eq]; simp)
    b_mem_nonnegative
    (by intro y hy; rw [steadyStateMap_eq] at hy; exact (sub_eq_zero.mp hy).symm)
    hfinN reducedJacobian_det_at_b_pos boundary_ne_zero

end DegreeExampleCheck

end Network

end CRNT
