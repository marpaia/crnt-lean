import CRNT.Multistationarity.DegreeStructural
import CRNT.Multistationarity.ParametrizedLocalDegree

/-!
# The Conradi–Feliu–Mincheva–Wiuf perturbation argument: two steady states in one class

This module supplies the **perturbation argument** of field-map leaf **M9** ("Brouwer degree and
steady-state existence").  It is the step that turns the *degree-theoretic* content of
`CRNT.Multistationarity.DegreeStructural` (the sign of the reduced Jacobian determinant at a
steady state is the local degree of the steady-state map there) into the Conradi–Feliu–Mincheva–Wiuf
conclusion:

> a compatibility class whose reduced Jacobian determinant has the "multistationary" sign at one of
> its steady states carries **at least two** distinct positive steady states.

## The classical argument, and how it is split here

Write `G : ℝ^s → ℝ^s` for the reduced field of the class (`Network.steadyStateMap`, the
mass-action field restricted to the compatibility class and read in the chart coordinates of the
class, `s = N.stoichRank`), and let `U` be the chart image of the (nonnegative) class.

1. **The degree.** The relative Brouwer degree of `G` on `U` (`Network.nonnegativeClassDegree`) is
   the *signed count* of the zeros of `G` in `U`, the summand at a zero `z` being the local degree
   `sign (det (D G z))` (`CRNT.localDegreeOn`).  For a mass-action network, Conradi et al. prove
   that this total is `(-1)^s` (their supporting information, Theorem 3): the field of a
   dissipative network points *inwards* on the boundary of the class, and the combined map
   `φ_c` (the field with `d = n - s` of its rows replaced by the rows of the conservation-relation
   matrix `W`) has degree `(-1)^s` on a suitable convex box.

2. **The counting.** If one zero `ystar` of `G` has local degree `(-1)^{s+1}` — the opposite of the
   total — then the remaining zeros cannot be absent: their local degrees would have to sum to
   `(-1)^s - (-1)^{s+1} ≠ 0`.  Hence the class carries at least two zeros, and (because the field
   does not vanish on the class boundary) at least two *positive* steady states.

3. **The perturbation.** Conradi et al. compute the total degree of step 1 by *perturbing* the
   field: the field `f` is replaced by the time-`T` averaged flow
   `g(x) = (φ(x,T) - x)/T + T ρ(x)`, which makes the field point strictly inwards on the boundary of
   a convex box `B_c`, so that the combined map can be homotoped to the affine map
   `(Wx - c, π(x̄ - x))`, whose Jacobian determinant is `(-1)^s`.  The degree-theoretic device used
   there is the one formalized in this module:

   * a *constant shift* of the field (`F ↦ F + ε v`, in chart coordinates `G ↦ G + c`) does **not**
     change the derivative, hence does not change the local degree at a regular preimage;
   * the relative degree of the shifted field equals that of the original field, as long as the
     homotopy `t ↦ G + t c` avoids `0` on the boundary of the region — this is the classical
     "the degree changes only by crossing the boundary" argument.

   The present module formalizes these two facts (items 3a and 3b below), together with the
   implicit-function-theorem step that produces a zero of the *perturbed* field near `ystar` with
   the *same* local degree.

## What is formalized here

* `localDegreeOn_add_const_singleton_eq_sign_det` — a constant shift does not change the local
  degree of a map at a regular preimage (general statement).
* `localDegreeOn_eq_of_subset_of_avoids_zero` — the "boundary bridge": the relative degree on a
  region equals that on a smaller one when the difference is a set on which the map does not
  vanish.
* `exists_other_zero_of_localDegreeOn_neg` — the **degree-counting lemma**: if the relative degree
  on a region is `d ≠ 0` and one of the zeros has local degree `-d`, there is another zero in the
  region.
* `Network.localDegreeOn_perturbedSteadyStateMap_singleton_eq_sign_reducedDet` — **the local part
  of the perturbation argument**: the local degree of the perturbed steady-state map at a regular
  preimage is the sign of the *unperturbed* reduced Jacobian determinant.
* `Network.exists_perturbed_zero_near_of_det_ne_zero` — **the implicit-function-theorem step**: for
  a small perturbation parameter `t` the perturbed map has a zero near the steady state `ystar`, and
  the local degree there is the sign of the reduced determinant at `ystar`.
* `Network.positiveClassDegree_eq_degree_perturbed` — **the degree-invariance step**: the relative
  degree of the perturbed map equals that of the unperturbed one along the homotopy
  `t ↦ G + t c`, provided the homotopy avoids `0` on the boundary of the class region.
* `Network.exists_two_positiveSteadyStates_of_classDegree_neg_localDegree` — **the counting
  step**, i.e. the Conradi–Feliu–Mincheva–Wiuf conclusion: a class whose degree is `d ≠ 0` and
  which contains a steady state of local degree `-d` carries two distinct positive steady states.
* `Network.exists_two_positiveSteadyStates_of_classDegree_eq_pow_neg_one` — the same conclusion in
  the published numerical form (total degree `(-1)^s`, exceptional local degree `(-1)^{s+1}`), and
  `Network.exists_two_positiveSteadyStates_of_classDegree_neg_pow_neg_one` — the same conclusion
  with both signs flipped (see the sign conventions below).
* `Network.exists_two_zeros_perturbed_of_classDegree_neg_localDegree` — the perturbed version of
  the counting step: the perturbed map itself carries two zeros in the class region, one of them
  near `ystar` and of the same local degree.
* `DegreeExampleCheck.classDegree_eq_pow_neg_one_stoichRank` — a consistency check: for the
  fully open two-species instance the class degree is `(-1)^s`, so the *total-degree* hypothesis of
  the published theorem holds there (while the exceptional sign condition fails, as it must).

## Sign conventions

* **Orientation.** The sign of the reduced determinant is read in the *chart orientation* of the
  class coordinates `Fin s → ℝ`: `Network.reducedJacobian κ x₀ y` is the matrix of the derivative
  of the reduced field `G`, so the local degree of the steady-state map at a regular preimage `y`
  is `sign (det (N.reducedJacobian κ x₀ y).det)`
  (`Network.localDegreeOn_steadyStateMap_singleton_eq_sign_reducedDet`).  In rank one the reduced
  determinant is the reduced derivative `φ'` of the scalar field along the class
  (`Network.reducedJacobian_det_eq_deriv`), so the local degree `+1` is the signature `φ' > 0`,
  i.e. the multistationary signature of `Network.rankOne_multistationary_iff_det_pos`.
* **The published determinant.** Conradi et al. use the determinant `det M(x*)` of the `n × n`
  matrix `M(x)` obtained from the Jacobian of the field by replacing `d = n - s` of its rows by the
  rows of the conservation-relation matrix `W`; this is the *core determinant* of the network
  (Helton–Klep–Gomez, Lemma 3.7, as the published paper notes).  It is the determinant of the
  field Jacobian restricted to the stoichiometric subspace, multiplied by a fixed nonzero factor (a
  minor of `W`), and read in the basis of `S(N)` determined by `W`.  It therefore differs from the
  library's chart-orientation reduced determinant by a **fixed sign**, which depends on the choice
  of `W` and of the chart basis; the docstring of
  `CRNT.Multistationarity.RankOneParameterRegion` records the published determinant as having the
  opposite sign in rank one, and the docstring of `CRNT.Multistationarity.DegreeStructural`
  repeats this.  Since the *total* degree and the *local* degree are affected by the same factor,
  the comparison is only meaningful between quantities read in one and the same orientation.  This
  is why the main theorem below is stated in the orientation-free form "the degree is `d` and the
  exceptional steady state has local degree `-d`": it is invariant under the fixed sign factor.
  The published numerical form (`(-1)^s` for the total degree and `(-1)^{s+1}` for the exceptional
  local degree) is recorded in a corollary, and the corollary with both signs flipped covers the
  opposite convention.
* **The total degree is a hypothesis.** The statement `Network.nonnegativeClassDegree κ x₀ hfin =
  (-1)^s` is the content of Conradi et al.'s Theorem 3 (supporting information), which requires
  the *dissipativity* of the network and the construction of an attracting set and of a bump
  function; it is *not* proved here and is carried as an explicit hypothesis.

## Relation to leaf M9

`CRNT.Multistationarity.DegreeExistence` gives the relative class degree and its existence
principle; `CRNT.Multistationarity.DegreeStructural` identifies the local degree at a steady state
with the sign of the reduced Jacobian determinant.  This module adds the perturbation device and
the counting step, and thereby the Conradi–Feliu–Mincheva–Wiuf conclusion in the class: **two
distinct positive steady states**.  The remaining gap of leaf M9 is the *total-degree theorem*
(the computation of `(-1)^s` for a given network), which in the published proof is itself a
perturbation argument and is not formalized here.

Depends on: `CRNT.Multistationarity.DegreeStructural`, `CRNT.Multistationarity.ParametrizedLocalDegree`.
-/

set_option maxHeartbeats 800000

namespace CRNT

open scoped BigOperators Topology Classical

open Set Filter

/-! ## The constant shift does not change the derivative -/

section ConstantShift

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **A constant shift does not change the local degree at a regular preimage.**  If `f y₀ + c = 0`,
then the relative degree of `y ↦ f y + c` at `0` on the one-point region `{y₀}` is the orientation
sign of the derivative of `f` at `y₀`: the shift is a constant, so it does not change the
derivative.  This is the local half of the Conradi–Feliu–Mincheva–Wiuf perturbation argument. -/
theorem localDegreeOn_add_const_singleton_eq_sign_det (f : E → E) (c : E) (y₀ : E)
    (hzero : f y₀ + c = 0)
    (hfin : ((fun y => f y + c) ⁻¹' {(0 : E)} ∩ {y₀}).Finite) :
    localDegreeOn (fun y => f y + c) 0 {y₀} hfin
      = ((SignType.sign (LinearMap.det (fderiv ℝ f y₀).toLinearMap) : SignType) : ℤ) := by
  rw [localDegreeOn_singleton (fun y => f y + c) y₀ hzero hfin]
  rw [fderiv_add_const]

end ConstantShift

/-- **The relative degree on a region equals that on a smaller one, when the difference is a set on
which the map does not vanish.**  This is the general form of the "boundary bridge" used to pass
from the positive part of a class to its nonnegative part: the zeros lost in the passage lie on the
boundary, where the field is assumed to be nonzero. -/
theorem localDegreeOn_eq_of_subset_of_avoids_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : E → E) {U V : Set E} {B : Set E}
    (hVU : ∀ x ∈ V, x ∈ U)
    (hUVB : ∀ x ∈ U, x ∈ V ∨ x ∈ B)
    (hne : ∀ x ∈ B, f x ≠ 0)
    (hfinU : (f ⁻¹' {(0 : E)} ∩ U).Finite) (hfinV : (f ⁻¹' {(0 : E)} ∩ V).Finite) :
    localDegreeOn f 0 U hfinU = localDegreeOn f 0 V hfinV := by
  have hset : f ⁻¹' {(0 : E)} ∩ U = f ⁻¹' {(0 : E)} ∩ V := by
    ext x
    constructor
    · intro hx
      refine ⟨hx.1, ?_⟩
      by_contra hxV
      have hxB : x ∈ B := by
        rcases hUVB x hx.2 with h | h
        · exact absurd h hxV
        · exact h
      exact hne x hxB hx.1
    · intro hx
      exact ⟨hx.1, hVU x hx.2⟩
  exact localDegreeOn_congr_of_preimage_inter_eq f 0 hset hfinU hfinV

/-- **The degree-counting lemma.**  The relative degree of `f` on `U` is the signed count of its
zeros in `U`; if that count is `d ≠ 0` and one of the zeros has local degree `-d`, then the zero
set cannot be exhausted by that single point: there is another zero of `f` in `U`, different from
it.  This is the counting step of the Conradi–Feliu–Mincheva–Wiuf argument. -/
theorem exists_other_zero_of_localDegreeOn_neg {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : E → E) {U : Set E}
    (hfin : (f ⁻¹' {(0 : E)} ∩ U).Finite)
    (hdeg : localDegreeOn f 0 U hfin ≠ 0)
    (y₀ : E) (hy₀ : y₀ ∈ U) (hzero : f y₀ = 0)
    (hlocal : ((SignType.sign (LinearMap.det (fderiv ℝ f y₀).toLinearMap) : SignType) : ℤ)
        = -(localDegreeOn f 0 U hfin)) :
    ∃ y ∈ U, f y = 0 ∧ y ≠ y₀ := by
  classical
  -- the degree is the signed count of the zeros in the region
  have hsum : (∑ x ∈ hfin.toFinset,
      ((SignType.sign (LinearMap.det (fderiv ℝ f x).toLinearMap) : SignType) : ℤ))
      = localDegreeOn f 0 U hfin := by
    rfl
  have hy₀fin : y₀ ∈ hfin.toFinset := by
    rw [hfin.mem_toFinset]
    exact ⟨hzero, hy₀⟩
  -- split off the contribution of `y₀`
  have hsplit : (∑ x ∈ hfin.toFinset,
        ((SignType.sign (LinearMap.det (fderiv ℝ f x).toLinearMap) : SignType) : ℤ))
      = (∑ x ∈ hfin.toFinset.erase y₀,
        ((SignType.sign (LinearMap.det (fderiv ℝ f x).toLinearMap) : SignType) : ℤ))
        + ((SignType.sign (LinearMap.det (fderiv ℝ f y₀).toLinearMap) : SignType) : ℤ) :=
    (Finset.sum_erase_add hfin.toFinset
      (fun x => ((SignType.sign (LinearMap.det (fderiv ℝ f x).toLinearMap) : SignType) : ℤ))
      hy₀fin).symm
  have hrest : (∑ x ∈ hfin.toFinset.erase y₀,
        ((SignType.sign (LinearMap.det (fderiv ℝ f x).toLinearMap) : SignType) : ℤ))
      = 2 * localDegreeOn f 0 U hfin := by
    have h2 : (∑ x ∈ hfin.toFinset.erase y₀,
          ((SignType.sign (LinearMap.det (fderiv ℝ f x).toLinearMap) : SignType) : ℤ))
        = (∑ x ∈ hfin.toFinset,
          ((SignType.sign (LinearMap.det (fderiv ℝ f x).toLinearMap) : SignType) : ℤ))
          - ((SignType.sign (LinearMap.det (fderiv ℝ f y₀).toLinearMap) : SignType) : ℤ) := by
      linarith [hsplit]
    rw [h2, hsum, hlocal]
    ring
  -- the remaining zeros cannot be absent
  have hne : (hfin.toFinset.erase y₀).Nonempty := by
    by_contra hcon
    have hempty : hfin.toFinset.erase y₀ = ∅ := Finset.not_nonempty_iff_eq_empty.mp hcon
    have hz0 : (2 : ℤ) * localDegreeOn f 0 U hfin = 0 := by
      rw [← hrest, hempty, Finset.sum_empty]
    have hd0 : localDegreeOn f 0 U hfin = 0 := by
      rcases mul_eq_zero.mp hz0 with h | h
      · norm_num at h
      · exact h
    have hfalse : False := absurd hd0 hdeg
    exact hfalse.elim
  obtain ⟨z, hz⟩ := hne
  have hzmem : z ∈ hfin.toFinset := Finset.mem_of_mem_erase hz
  have hzne : z ≠ y₀ := (Finset.mem_erase.mp hz).1
  have hzset : z ∈ f ⁻¹' {(0 : E)} ∩ U := hfin.mem_toFinset.mp hzmem
  have hzpre : f z = 0 := Set.mem_singleton_iff.mp hzset.1
  exact ⟨z, hzset.2, hzpre, hzne⟩


namespace Network

open scoped BigOperators Topology Classical

open Set Filter

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **The nonnegative class region is the union of the positive region and the class boundary.**
This is the form of `Network.nonnegativeClassRegion_eq_positive_union_boundary` used below. -/
theorem mem_nonnegativeClassRegion_iff_pos_or_boundary (N : Network S) (x₀ : Concentration S) (y : ClassCoord N) :
    y ∈ N.nonnegativeClassRegion x₀ ↔
      y ∈ N.positiveClassRegion x₀ ∨ y ∈ N.classBoundary x₀ := by
  rw [N.nonnegativeClassRegion_eq_positive_union_boundary x₀]
  exact Set.mem_union y _ _

/-! ## The perturbed reduced field -/

/-- **The perturbed reduced field.**  This is the reduced field `G = N.steadyStateMap κ x₀` shifted
by the constant vector `c` of the class: `y ↦ G y + c`.  It is the chart form of the classical
perturbation `F_ε(y) = F(y) + ε • v` of the mass-action field along the class direction `v`, with
`c = ε • v`. -/
noncomputable def perturbedSteadyStateMap (N : Network S) (κ : N.RateConstants)
    (x₀ : Concentration S) (c : ClassCoord N) : ClassCoord N → ClassCoord N :=
  fun y => N.steadyStateMap κ x₀ y + c

@[simp] theorem perturbedSteadyStateMap_apply (N : Network S) (κ : N.RateConstants)
    (x₀ : Concentration S) (c : ClassCoord N) (y : ClassCoord N) :
    N.perturbedSteadyStateMap κ x₀ c y = N.steadyStateMap κ x₀ y + c := rfl

/-- The zeros of the perturbed field are the points where the unperturbed field takes the value
`-c`. -/
theorem perturbedSteadyStateMap_eq_zero_iff (N : Network S) (κ : N.RateConstants)
    (x₀ : Concentration S) (c : ClassCoord N) (y : ClassCoord N) :
    N.perturbedSteadyStateMap κ x₀ c y = 0 ↔ N.steadyStateMap κ x₀ y = -c := by
  simp only [perturbedSteadyStateMap_apply, add_eq_zero_iff_eq_neg]

/-- **The perturbation does not change the derivative.**  The derivative of the perturbed reduced
field at `y` is the reduced Jacobian operator at `y`, exactly as for the unperturbed field. -/
theorem fderiv_perturbedSteadyStateMap (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S)
    (c : ClassCoord N) (y : ClassCoord N) :
    fderiv ℝ (N.perturbedSteadyStateMap κ x₀ c) y = N.reducedJacobianCLM κ x₀ y := by
  have hG : fderiv ℝ (N.steadyStateMap κ x₀) y = N.reducedJacobianCLM κ x₀ y := by
    simpa only [Network.steadyStateMap] using (N.reducedField_hasFDerivAt κ x₀ y).fderiv
  rw [show N.perturbedSteadyStateMap κ x₀ c = fun z => N.steadyStateMap κ x₀ z + c by
        funext z; exact N.perturbedSteadyStateMap_apply κ x₀ c z]
  rw [fderiv_add_const]
  exact hG

/-- **The determinant of the derivative of the perturbed field is the reduced Jacobian
determinant.** -/
theorem det_fderiv_perturbedSteadyStateMap_eq_reducedJacobian_det (N : Network S)
    (κ : N.RateConstants) (x₀ : Concentration S) (c : ClassCoord N) (y : ClassCoord N) :
    LinearMap.det (fderiv ℝ (N.perturbedSteadyStateMap κ x₀ c) y).toLinearMap
      = (N.reducedJacobian κ x₀ y).det := by
  rw [N.fderiv_perturbedSteadyStateMap κ x₀ c y]
  have h1 : LinearMap.det (N.reducedJacobianCLM κ x₀ y).toLinearMap
      = (jacobianMatrix (N.reducedJacobianCLM κ x₀ y)).det := by
    rw [jacobianMatrix_det]
  rw [h1, N.jacobianMatrix_reducedField]

/-- **The local degree of the perturbed map at a regular preimage is the sign of the unperturbed
reduced Jacobian determinant.**  This is the *local* half of the Conradi–Feliu–Mincheva–Wiuf
perturbation argument: at a zero `y₀` of the perturbed field `G + c`, the local degree of `G + c` is
`sign (det (D G y₀))`, i.e. the sign of the reduced Jacobian determinant of the *original* field at
`y₀`.  A positive reduced determinant therefore gives the local degree `+1` for the perturbed map
as well. -/
theorem localDegreeOn_perturbedSteadyStateMap_singleton_eq_sign_reducedDet
    (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S) (c : ClassCoord N)
    (y₀ : ClassCoord N) (hzero : N.perturbedSteadyStateMap κ x₀ c y₀ = 0)
    (hfin : (N.perturbedSteadyStateMap κ x₀ c ⁻¹' {0} ∩ {y₀}).Finite) :
    localDegreeOn (N.perturbedSteadyStateMap κ x₀ c) 0 {y₀} hfin
      = ((SignType.sign (N.reducedJacobian κ x₀ y₀).det : SignType) : ℤ) := by
  have hfin' : ((fun y => N.steadyStateMap κ x₀ y + c) ⁻¹' {(0 : ClassCoord N)} ∩ {y₀}).Finite := by
    exact hfin
  have hzero' : N.steadyStateMap κ x₀ y₀ + c = 0 := by
    simpa only [perturbedSteadyStateMap_apply] using hzero
  have hlg : localDegreeOn (N.perturbedSteadyStateMap κ x₀ c) 0 {y₀} hfin
      = localDegreeOn (fun y => N.steadyStateMap κ x₀ y + c) 0 {y₀} hfin' := by
    unfold localDegreeOn
    congr 1
  rw [hlg]
  rw [localDegreeOn_add_const_singleton_eq_sign_det (N.steadyStateMap κ x₀) c y₀ hzero' hfin']
  rw [N.det_fderiv_steadyStateMap_eq_reducedJacobian_det]

/-- **The local degree of the perturbed map on a region with a unique preimage is the sign of the
unperturbed reduced Jacobian determinant at that preimage.** -/
theorem localDegreeOn_perturbedSteadyStateMap_eq_sign_reducedDet_of_unique_preimage
    (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S) (c : ClassCoord N)
    (y₀ : ClassCoord N) (hzero : N.perturbedSteadyStateMap κ x₀ c y₀ = 0)
    (huniq : ∀ y, N.perturbedSteadyStateMap κ x₀ c y = 0 → y = y₀)
    {U : Set (ClassCoord N)} (hy₀ : y₀ ∈ U)
    (hfin : (N.perturbedSteadyStateMap κ x₀ c ⁻¹' {0} ∩ U).Finite) :
    localDegreeOn (N.perturbedSteadyStateMap κ x₀ c) 0 U hfin
      = ((SignType.sign (N.reducedJacobian κ x₀ y₀).det : SignType) : ℤ) := by
  rw [localDegreeOn_eq_sign_det_of_unique_preimage (N.perturbedSteadyStateMap κ x₀ c) y₀ hzero
    huniq hy₀ hfin]
  rw [N.det_fderiv_perturbedSteadyStateMap_eq_reducedJacobian_det]

/-! ## The perturbation homotopy -/

/-- **The perturbation homotopy.**  At parameter `t` the slice is the reduced field shifted by
`t • c`; the slice at `t = 0` is the unperturbed reduced field and the slice at `t = 1` is the
perturbed one. -/
noncomputable def perturbedHomotopy (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S)
    (c : ClassCoord N) : ℝ × ClassCoord N → ClassCoord N :=
  fun p => N.steadyStateMap κ x₀ p.2 + p.1 • c

@[simp] theorem perturbedHomotopy_apply_zero (N : Network S) (κ : N.RateConstants)
    (x₀ : Concentration S) (c : ClassCoord N) (y : ClassCoord N) :
    N.perturbedHomotopy κ x₀ c (0, y) = N.steadyStateMap κ x₀ y := by
  simp [perturbedHomotopy]

@[simp] theorem perturbedHomotopy_apply_one (N : Network S) (κ : N.RateConstants)
    (x₀ : Concentration S) (c : ClassCoord N) (y : ClassCoord N) :
    N.perturbedHomotopy κ x₀ c (1, y) = N.perturbedSteadyStateMap κ x₀ c y := by
  simp [perturbedHomotopy, perturbedSteadyStateMap]

/-- The perturbation homotopy is smooth. -/
theorem perturbedHomotopy_contDiff (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S)
    (c : ClassCoord N) : ContDiff ℝ 1 (N.perturbedHomotopy κ x₀ c) := by
  have h0 : ContDiff ℝ 1 (fun p : ℝ × ClassCoord N =>
      N.steadyStateMap κ x₀ p.2) :=
    (N.steadyStateMap_contDiff (n := 1) κ x₀).comp contDiff_snd
  have hc : ContDiff ℝ 1 (fun p : ℝ × ClassCoord N => p.1 • c) :=
    contDiff_fst.smul contDiff_const
  change ContDiff ℝ 1 (fun p : ℝ × ClassCoord N =>
    N.steadyStateMap κ x₀ p.2 + p.1 • c)
  exact h0.add hc

/-- **The derivative of the slices of the perturbation homotopy is the reduced Jacobian.**  The
shift does not change the derivative, so the `s`-derivative of the homotopy at `(t, y)` is the
reduced Jacobian operator at `y`. -/
theorem partialFDeriv_perturbedHomotopy (N : Network S) (κ : N.RateConstants)
    (x₀ : Concentration S) (c : ClassCoord N) (t : ℝ) (y : ClassCoord N) :
    partialFDeriv (N.perturbedHomotopy κ x₀ c) (t, y) = N.reducedJacobianCLM κ x₀ y := by
  have hH : DifferentiableAt ℝ (N.perturbedHomotopy κ x₀ c) (t, y) :=
    (N.perturbedHomotopy_contDiff κ x₀ c).contDiffAt.differentiableAt
      (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have hslice : HasFDerivAt (fun x => N.perturbedHomotopy κ x₀ c (t, x))
      (partialFDeriv (N.perturbedHomotopy κ x₀ c) (t, y)) y := by
    have h := hasFDerivAt_slice (N.perturbedHomotopy κ x₀ c) hH
    simpa only using h
  have hslice' : fderiv ℝ (fun x => N.perturbedHomotopy κ x₀ c (t, x)) y
      = fderiv ℝ (fun x => N.steadyStateMap κ x₀ x + t • c) y := by
    have hfun : (fun x => N.perturbedHomotopy κ x₀ c (t, x))
        = (fun x => N.steadyStateMap κ x₀ x + t • c) := by
      funext x
      simp [perturbedHomotopy]
    rw [hfun]
  have hG : fderiv ℝ (N.steadyStateMap κ x₀) y = N.reducedJacobianCLM κ x₀ y := by
    simpa only [Network.steadyStateMap] using (N.reducedField_hasFDerivAt κ x₀ y).fderiv
  calc partialFDeriv (N.perturbedHomotopy κ x₀ c) (t, y)
      = fderiv ℝ (fun x => N.perturbedHomotopy κ x₀ c (t, x)) y := hslice.fderiv.symm
    _ = fderiv ℝ (fun x => N.steadyStateMap κ x₀ x + t • c) y := hslice'
    _ = fderiv ℝ (N.steadyStateMap κ x₀) y := fderiv_add_const (t • c)
    _ = N.reducedJacobianCLM κ x₀ y := hG

/-- **The determinant of the slice derivative of the perturbation homotopy is the reduced Jacobian
determinant.**  In particular, the nondegeneracy of the perturbed map at a zero is exactly the
nondegeneracy of the unperturbed reduced Jacobian there. -/
theorem det_partialFDeriv_perturbedHomotopy_eq_reducedJacobian_det (N : Network S)
    (κ : N.RateConstants) (x₀ : Concentration S) (c : ClassCoord N) (t : ℝ) (y : ClassCoord N) :
    LinearMap.det (partialFDeriv (N.perturbedHomotopy κ x₀ c) (t, y)).toLinearMap
      = (N.reducedJacobian κ x₀ y).det := by
  rw [N.partialFDeriv_perturbedHomotopy κ x₀ c t y]
  have h1 : LinearMap.det (N.reducedJacobianCLM κ x₀ y).toLinearMap
      = (jacobianMatrix (N.reducedJacobianCLM κ x₀ y)).det := by
    rw [jacobianMatrix_det]
  rw [h1, N.jacobianMatrix_reducedField]

/-! ## The perturbation creates a nearby zero with the same local degree -/

/-- **The perturbation produces a nearby zero of the perturbed map, with the same local degree.**

This is the implicit-function-theorem step of the Conradi–Feliu–Mincheva–Wiuf perturbation
argument.  Let `ystar` be a *nondegenerate* zero of the reduced field (`G ystar = 0` and the reduced
Jacobian determinant at `ystar` nonzero).  Then for all sufficiently small `t` the perturbed map
`G + t • c` has a zero `y` arbitrarily close to `ystar`, and the local degree of the perturbed map at
`y` is the sign of the reduced Jacobian determinant at `ystar`: the perturbation is a constant shift,
so it does not change the derivative, and the sign of the determinant is locally constant.

In particular, a positive reduced determinant at `ystar` gives local degree `+1` for the perturbed map
at the nearby zero. -/
theorem exists_perturbed_zero_near_of_det_ne_zero
    (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S) (c : ClassCoord N)
    (ystar : ClassCoord N) (hzero : N.steadyStateMap κ x₀ ystar = 0)
    (hdet : (N.reducedJacobian κ x₀ ystar).det ≠ 0)
    {V₀ : Set (ClassCoord N)} (hV₀ : V₀ ∈ 𝓝 ystar) :
    ∃ V : Set (ClassCoord N), V ⊆ V₀ ∧ IsOpen V ∧ ystar ∈ V ∧
      ∀ᶠ t in 𝓝 (0 : ℝ), ∃ y ∈ V,
        N.perturbedSteadyStateMap κ x₀ (t • c) y = 0 ∧
        ((SignType.sign (N.reducedJacobian κ x₀ y).det : SignType) : ℤ) =
          ((SignType.sign (N.reducedJacobian κ x₀ ystar).det : SignType) : ℤ) := by
  have hH : ContDiffAt ℝ 1 (N.perturbedHomotopy κ x₀ c) (0, ystar) :=
    (N.perturbedHomotopy_contDiff κ x₀ c).contDiffAt
  have hdet' : LinearMap.det (partialFDeriv (N.perturbedHomotopy κ x₀ c) (0, ystar)).toLinearMap ≠ 0 := by
    rw [N.det_partialFDeriv_perturbedHomotopy_eq_reducedJacobian_det]
    exact hdet
  obtain ⟨V, hVV₀, hVopen, hystarV, hev⟩ :=
    exists_eventually_slice_singleton (N.perturbedHomotopy κ x₀ c) hH hdet' hV₀
  refine ⟨V, hVV₀, hVopen, hystarV, ?_⟩
  filter_upwards [hev] with t ht
  obtain ⟨y, hyV, hset, hsign⟩ := ht
  refine ⟨y, hyV, ?_, ?_⟩
  · -- the perturbed field vanishes at `y`
    have hmem : y ∈ (fun z => N.perturbedHomotopy κ x₀ c (t, z)) ⁻¹'
        {N.perturbedHomotopy κ x₀ c (0, ystar)} := by
      have hmem' : y ∈ (fun z => N.perturbedHomotopy κ x₀ c (t, z)) ⁻¹'
          {N.perturbedHomotopy κ x₀ c (0, ystar)} ∩ V := by
        rw [hset]
        simp
      exact hmem'.1
    have hval : N.perturbedHomotopy κ x₀ c (t, y) = N.perturbedHomotopy κ x₀ c (0, ystar) := by
      have hval' := hmem
      rw [Set.mem_preimage, Set.mem_singleton_iff] at hval'
      exact hval'
    have hzero' : N.perturbedHomotopy κ x₀ c (0, ystar) = 0 := by
      simp [perturbedHomotopy, hzero]
    have : N.perturbedSteadyStateMap κ x₀ (t • c) y = 0 := by
      have hh : N.perturbedSteadyStateMap κ x₀ (t • c) y
          = N.perturbedHomotopy κ x₀ c (t, y) := by
        simp [perturbedSteadyStateMap, perturbedHomotopy]
      rw [hh, hval, hzero']
    exact this
  · -- the local degree of the perturbed map at `y` is the one of the unperturbed map at `ystar`
    have hslice : fderiv ℝ (fun z => N.perturbedHomotopy κ x₀ c (t, z)) y
        = fderiv ℝ (N.steadyStateMap κ x₀) y := by
      have hfun : (fun z => N.perturbedHomotopy κ x₀ c (t, z))
          = (fun z => N.steadyStateMap κ x₀ z + t • c) := by
        funext z
        simp [perturbedHomotopy]
      rw [hfun, fderiv_add_const]
    rw [hslice] at hsign
    rw [N.det_fderiv_steadyStateMap_eq_reducedJacobian_det] at hsign
    rw [N.det_partialFDeriv_perturbedHomotopy_eq_reducedJacobian_det] at hsign
    exact congrArg (fun s : SignType => (s : ℤ)) hsign

/-! ## The degree of the perturbed map -/

/-- **The relative degree of the perturbed map equals that of the unperturbed map.**  This is the
"the degree changes only by crossing the boundary" step of the Conradi–Feliu–Mincheva–Wiuf
argument: along the homotopy `t ↦ G + t c` the relative degree on the class region is constant,
provided the homotopy avoids `0` on the boundary of the region, the zeros are nondegenerate, and
the zero sets are finite. -/
theorem positiveClassDegree_eq_degree_perturbed
    (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S) (c : ClassCoord N)
    (hUcpt : IsCompact (closure (N.positiveClassRegion x₀)))
    (hbd : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ closure (N.positiveClassRegion x₀),
      N.perturbedHomotopy κ x₀ c (t, y) = 0 → y ∈ N.positiveClassRegion x₀)
    (hreg : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ N.positiveClassRegion x₀,
      N.perturbedHomotopy κ x₀ c (t, y) = 0 →
      LinearMap.det (partialFDeriv (N.perturbedHomotopy κ x₀ c) (t, y)).toLinearMap ≠ 0)
    (hfin : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ((fun y => N.perturbedHomotopy κ x₀ c (t, y)) ⁻¹' {0} ∩ N.positiveClassRegion x₀).Finite)
    (hfinP : (N.steadyStateMap κ x₀ ⁻¹' {0} ∩ N.positiveClassRegion x₀).Finite)
    (hfinQ : (N.perturbedSteadyStateMap κ x₀ c ⁻¹' {0} ∩ N.positiveClassRegion x₀).Finite) :
    N.positiveClassDegree κ x₀ hfinP
      = localDegreeOn (N.perturbedSteadyStateMap κ x₀ c) 0 (N.positiveClassRegion x₀) hfinQ := by
  have hmain := localDegreeOn_homotopy_invariant (N.perturbedHomotopy κ x₀ c)
    (N.perturbedHomotopy_contDiff κ x₀ c)
    (N.isOpen_positiveClassRegion x₀) hUcpt hbd hreg hfin
    (by norm_num : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
    (by norm_num : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
  -- the two slices of the homotopy are the unperturbed and the perturbed reduced field
  have hfun0 : ∀ x, N.perturbedHomotopy κ x₀ c (0, x) = N.steadyStateMap κ x₀ x := by
    intro x
    funext i
    simp [perturbedHomotopy]
  have hfun1 : ∀ x, N.perturbedHomotopy κ x₀ c (1, x)
      = N.perturbedSteadyStateMap κ x₀ c x := by
    intro x
    funext i
    simp [perturbedHomotopy, perturbedSteadyStateMap]
  have h0 := localDegreeOn_congr_fun (f := fun x => N.perturbedHomotopy κ x₀ c (0, x))
    (g := N.steadyStateMap κ x₀) (by funext x; exact hfun0 x) 0 (N.positiveClassRegion x₀)
    (hfin 0 (by norm_num : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1)) hfinP
  have h1 := localDegreeOn_congr_fun (f := fun x => N.perturbedHomotopy κ x₀ c (1, x))
    (g := N.perturbedSteadyStateMap κ x₀ c) (by funext x; exact hfun1 x) 0
    (N.positiveClassRegion x₀) (hfin 1 (by norm_num : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1)) hfinQ
  unfold positiveClassDegree
  exact (h0.symm ▸ hmain) ▸ h1

/-- **The class degree of the perturbed map equals that of the unperturbed map.**  This is the
same statement on the *nonnegative* part of the class; it follows from the positive-part statement
by the boundary bridge, which needs the non-vanishing of both fields on the class boundary. -/
theorem nonnegativeClassDegree_eq_degree_perturbed
    (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S) (c : ClassCoord N)
    (hUcpt : IsCompact (closure (N.positiveClassRegion x₀)))
    (hbd : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ closure (N.positiveClassRegion x₀),
      N.perturbedHomotopy κ x₀ c (t, y) = 0 → y ∈ N.positiveClassRegion x₀)
    (hreg : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ N.positiveClassRegion x₀,
      N.perturbedHomotopy κ x₀ c (t, y) = 0 →
      LinearMap.det (partialFDeriv (N.perturbedHomotopy κ x₀ c) (t, y)).toLinearMap ≠ 0)
    (hfin : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ((fun y => N.perturbedHomotopy κ x₀ c (t, y)) ⁻¹' {0} ∩ N.positiveClassRegion x₀).Finite)
    (hfinN : (N.steadyStateMap κ x₀ ⁻¹' {0} ∩ N.nonnegativeClassRegion x₀).Finite)
    (hfinNQ : (N.perturbedSteadyStateMap κ x₀ c ⁻¹' {0} ∩ N.nonnegativeClassRegion x₀).Finite)
    (hbd₀ : ∀ y ∈ N.classBoundary x₀, N.steadyStateMap κ x₀ y ≠ 0)
    (hbd₁ : ∀ y ∈ N.classBoundary x₀, N.perturbedSteadyStateMap κ x₀ c y ≠ 0) :
    N.nonnegativeClassDegree κ x₀ hfinN
      = localDegreeOn (N.perturbedSteadyStateMap κ x₀ c) 0 (N.nonnegativeClassRegion x₀) hfinNQ := by
  have hfinP : (N.steadyStateMap κ x₀ ⁻¹' {0} ∩ N.positiveClassRegion x₀).Finite :=
    hfinN.subset fun y hy => ⟨hy.1,
      (mem_positiveClassRegion_iff N x₀ y).mp hy.2 |>.nonnegative⟩
  have hfinPQ : (N.perturbedSteadyStateMap κ x₀ c ⁻¹' {0} ∩ N.positiveClassRegion x₀).Finite :=
    hfinNQ.subset fun y hy => ⟨hy.1,
      (mem_positiveClassRegion_iff N x₀ y).mp hy.2 |>.nonnegative⟩
  have hdegP := N.positiveClassDegree_eq_degree_perturbed κ x₀ c hUcpt hbd hreg hfin hfinP hfinPQ
  have hdeg₀ := localDegreeOn_eq_of_subset_of_avoids_zero (N.steadyStateMap κ x₀)
    (U := N.nonnegativeClassRegion x₀) (V := N.positiveClassRegion x₀)
    (B := N.classBoundary x₀)
    (fun y hy => (mem_nonnegativeClassRegion_iff N x₀ y).mp
      ((mem_positiveClassRegion_iff N x₀ y).mp hy |>.nonnegative))
    (fun y hy => (N.mem_nonnegativeClassRegion_iff_pos_or_boundary x₀ y).mp hy)
    (fun y hy => hbd₀ y hy) hfinN hfinP
  have hdeg₁ := localDegreeOn_eq_of_subset_of_avoids_zero (N.perturbedSteadyStateMap κ x₀ c)
    (U := N.nonnegativeClassRegion x₀) (V := N.positiveClassRegion x₀)
    (B := N.classBoundary x₀)
    (fun y hy => (mem_nonnegativeClassRegion_iff N x₀ y).mp
      ((mem_positiveClassRegion_iff N x₀ y).mp hy |>.nonnegative))
    (fun y hy => (N.mem_nonnegativeClassRegion_iff_pos_or_boundary x₀ y).mp hy)
    (fun y hy => hbd₁ y hy) hfinNQ hfinPQ
  have hdegP' : localDegreeOn (N.steadyStateMap κ x₀) 0 (N.positiveClassRegion x₀) hfinP
      = localDegreeOn (N.perturbedSteadyStateMap κ x₀ c) 0 (N.positiveClassRegion x₀) hfinPQ := by
    exact hdegP
  unfold nonnegativeClassDegree
  rw [hdeg₀, hdegP', hdeg₁.symm]

/-- **The perturbed field and the slice of the perturbation homotopy agree.** -/
theorem perturbedSteadyStateMap_eq_perturbedHomotopy_slice (N : Network S) (κ : N.RateConstants)
    (x₀ : Concentration S) (c : ClassCoord N) (t : ℝ) (y : ClassCoord N) :
    N.perturbedSteadyStateMap κ x₀ (t • c) y = N.perturbedHomotopy κ x₀ c (t, y) := by
  simp [perturbedSteadyStateMap, perturbedHomotopy]

/-- **The zero set of the perturbed field is the zero set of the slice of the homotopy.** -/
theorem perturbedSteadyStateMap_preimage_eq (N : Network S) (κ : N.RateConstants)
    (x₀ : Concentration S) (c : ClassCoord N) (t : ℝ) :
    (fun y => N.perturbedHomotopy κ x₀ c (t, y)) ⁻¹' {0}
      = N.perturbedSteadyStateMap κ x₀ (t • c) ⁻¹' {0} := by
  ext y
  rw [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_preimage, Set.mem_singleton_iff]
  rw [N.perturbedSteadyStateMap_eq_perturbedHomotopy_slice]

/-! ## The counting: the Conradi–Feliu–Mincheva–Wiuf conclusion -/

/-- **The Conradi–Feliu–Mincheva–Wiuf conclusion.**  Let the class degree of the reduced field on
the nonnegative part of the class be `d ≠ 0`, and let `ystar` be a steady state of the class whose
*local degree* — the sign of the reduced Jacobian determinant there — is `-d`.  Then the class
carries **two distinct positive steady states**.

This is the counting step of the published argument: the class degree is the signed count of the
zeros of the reduced field in the class, the contribution of `ystar` is `-d`, so the contributions
of the remaining zeros sum to `d - (-d) = 2d ≠ 0`, and hence there is at least one further zero.
Because the field does not vanish on the class boundary, both zeros are positive steady states.

In the published orientation the total degree is `(-1)^s` and the exceptional local degree is
`(-1)^{s+1}`; see `Network.exists_two_positiveSteadyStates_of_classDegree_eq_pow_neg_one`. -/
theorem exists_two_positiveSteadyStates_of_classDegree_neg_localDegree
    (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S) (ystar : ClassCoord N)
    (hzero : N.steadyStateMap κ x₀ ystar = 0)
    (hystar : ystar ∈ N.nonnegativeClassRegion x₀)
    (hfin : (N.steadyStateMap κ x₀ ⁻¹' {0} ∩ N.nonnegativeClassRegion x₀).Finite)
    (hdeg : N.nonnegativeClassDegree κ x₀ hfin ≠ 0)
    (hlocal : ((SignType.sign (N.reducedJacobian κ x₀ ystar).det : SignType) : ℤ)
        = -(N.nonnegativeClassDegree κ x₀ hfin))
    (hbd : ∀ y ∈ N.classBoundary x₀, N.steadyStateMap κ x₀ y ≠ 0) :
    ∃ x y : Concentration S,
      x ≠ y ∧ N.StoichCompatible x₀ x ∧ Concentration.Positive x ∧ N.IsMassActionSteadyState κ x ∧
      N.StoichCompatible x₀ y ∧ Concentration.Positive y ∧ N.IsMassActionSteadyState κ y := by
  -- the local degree of the unperturbed map at `ystar` is the sign of the reduced determinant
  have hlocal' : ((SignType.sign (LinearMap.det
      (fderiv ℝ (N.steadyStateMap κ x₀) ystar).toLinearMap) : SignType) : ℤ)
      = -(N.nonnegativeClassDegree κ x₀ hfin) := by
    rw [N.det_fderiv_steadyStateMap_eq_reducedJacobian_det]
    exact hlocal
  -- the counting step: a second zero of the reduced field in the class
  obtain ⟨z, hzreg, hzzero, hzne⟩ :=
    exists_other_zero_of_localDegreeOn_neg (N.steadyStateMap κ x₀)
      (U := N.nonnegativeClassRegion x₀) hfin hdeg ystar hystar hzero hlocal'
  -- the two zeros are positive: the field does not vanish on the class boundary
  have hystarpos : ystar ∈ N.positiveClassRegion x₀ := by
    rw [mem_positiveClassRegion_iff]
    by_contra hnp
    exact hbd ystar ⟨hystar, hnp⟩ hzero
  have hzpos : z ∈ N.positiveClassRegion x₀ := by
    rw [mem_positiveClassRegion_iff]
    by_contra hnp
    exact hbd z ⟨hzreg, hnp⟩ hzzero
  obtain ⟨hc1, hs1⟩ := N.isMassActionSteadyState_affineChart_of_reducedField_eq_zero κ x₀ hzero
  obtain ⟨hc2, hs2⟩ := N.isMassActionSteadyState_affineChart_of_reducedField_eq_zero κ x₀ hzzero
  refine ⟨N.affineChart x₀ ystar, N.affineChart x₀ z, ?_, hc1, hystarpos, hs1, hc2, hzpos, hs2⟩
  exact fun heq => hzne (N.affineChart_injective x₀ heq.symm)

/-- **The Conradi–Feliu–Mincheva–Wiuf conclusion in the published numerical form.**  If the class
degree of the reduced field on the nonnegative part of the class is `(-1)^s` (the total-degree
hypothesis of the published theorem) and the reduced Jacobian determinant at a steady state of the
class has the sign `(-1)^{s+1}` (the "multistationary" signature), then the class carries **two
distinct positive steady states**.

The two hypotheses are read in one and the same orientation (the chart orientation of the class
coordinates), so that the conclusion does not depend on the fixed sign factor relating the published
determinant `det M(x*)` to the chart-orientation reduced determinant. -/
theorem exists_two_positiveSteadyStates_of_classDegree_eq_pow_neg_one
    (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S) (ystar : ClassCoord N)
    (hzero : N.steadyStateMap κ x₀ ystar = 0)
    (hystar : ystar ∈ N.nonnegativeClassRegion x₀)
    (hfin : (N.steadyStateMap κ x₀ ⁻¹' {0} ∩ N.nonnegativeClassRegion x₀).Finite)
    (hdeg : N.nonnegativeClassDegree κ x₀ hfin = (-1 : ℤ) ^ N.stoichRank)
    (hdet : ((SignType.sign (N.reducedJacobian κ x₀ ystar).det : SignType) : ℤ)
        = (-1 : ℤ) ^ (N.stoichRank + 1))
    (hbd : ∀ y ∈ N.classBoundary x₀, N.steadyStateMap κ x₀ y ≠ 0) :
    ∃ x y : Concentration S,
      x ≠ y ∧ N.StoichCompatible x₀ x ∧ Concentration.Positive x ∧ N.IsMassActionSteadyState κ x ∧
      N.StoichCompatible x₀ y ∧ Concentration.Positive y ∧ N.IsMassActionSteadyState κ y := by
  refine N.exists_two_positiveSteadyStates_of_classDegree_neg_localDegree κ x₀ ystar hzero
    hystar hfin ?_ ?_ hbd
  · rw [hdeg]
    exact pow_ne_zero _ (by norm_num : (-1 : ℤ) ≠ 0)
  · rw [hdeg, hdet, pow_succ]
    ring

/-- **The Conradi–Feliu–Mincheva–Wiuf conclusion with the opposite sign convention.**  The same
statement as `Network.exists_two_positiveSteadyStates_of_classDegree_eq_pow_neg_one`, with both
signs flipped: the total degree is `-((-1)^s)` and the exceptional local degree is
`-((-1)^{s+1})`.  This covers the case in which the published determinant `det M(x*)` differs from
the library's chart-orientation reduced determinant by the fixed sign factor `-1` (see the sign
conventions in the module docstring). -/
theorem exists_two_positiveSteadyStates_of_classDegree_neg_pow_neg_one
    (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S) (ystar : ClassCoord N)
    (hzero : N.steadyStateMap κ x₀ ystar = 0)
    (hystar : ystar ∈ N.nonnegativeClassRegion x₀)
    (hfin : (N.steadyStateMap κ x₀ ⁻¹' {0} ∩ N.nonnegativeClassRegion x₀).Finite)
    (hdeg : N.nonnegativeClassDegree κ x₀ hfin = -((-1 : ℤ) ^ N.stoichRank))
    (hdet : ((SignType.sign (N.reducedJacobian κ x₀ ystar).det : SignType) : ℤ)
        = -((-1 : ℤ) ^ (N.stoichRank + 1)))
    (hbd : ∀ y ∈ N.classBoundary x₀, N.steadyStateMap κ x₀ y ≠ 0) :
    ∃ x y : Concentration S,
      x ≠ y ∧ N.StoichCompatible x₀ x ∧ Concentration.Positive x ∧ N.IsMassActionSteadyState κ x ∧
      N.StoichCompatible x₀ y ∧ Concentration.Positive y ∧ N.IsMassActionSteadyState κ y := by
  refine N.exists_two_positiveSteadyStates_of_classDegree_neg_localDegree κ x₀ ystar hzero
    hystar hfin ?_ ?_ hbd
  · rw [hdeg]
    have hp : (-1 : ℤ) ^ N.stoichRank ≠ 0 := pow_ne_zero _ (by norm_num : (-1 : ℤ) ≠ 0)
    intro h
    simp only [neg_eq_zero] at h
    exact hp h
  · rw [hdeg, hdet, pow_succ]
    ring

/-- **The perturbed map carries two zeros in the class region.**  This is the perturbed form of the
counting step: for a small perturbation parameter `t`, the perturbed map `G + t • c` has a zero
`z₁` near the steady state `ystar` — with the same local degree, by
`Network.exists_perturbed_zero_near_of_det_ne_zero` — and, since the relative degree of the
perturbed map is the class degree `d` and the local degree at `z₁` is `-d`, a second zero `z₂` in
the class region. -/
theorem exists_two_zeros_perturbed_of_classDegree_neg_localDegree
    (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S) (c : ClassCoord N)
    (ystar : ClassCoord N)
    (hzero : N.steadyStateMap κ x₀ ystar = 0)
    (hystar : ystar ∈ N.positiveClassRegion x₀)
    (hdet : (N.reducedJacobian κ x₀ ystar).det ≠ 0)
    (hfin : (N.steadyStateMap κ x₀ ⁻¹' {0} ∩ N.positiveClassRegion x₀).Finite)
    (hdeg : N.positiveClassDegree κ x₀ hfin ≠ 0)
    (hlocal : ((SignType.sign (N.reducedJacobian κ x₀ ystar).det : SignType) : ℤ)
        = -(N.positiveClassDegree κ x₀ hfin))
    (hUcpt : IsCompact (closure (N.positiveClassRegion x₀)))
    (hbdH : ∀ (t s : ℝ), 0 ≤ s → s ≤ 1 → ∀ y ∈ closure (N.positiveClassRegion x₀),
        N.perturbedHomotopy κ x₀ (t • c) (s, y) = 0 → y ∈ N.positiveClassRegion x₀)
    (hregH : ∀ (t s : ℝ), 0 ≤ s → s ≤ 1 → ∀ y ∈ N.positiveClassRegion x₀,
        N.perturbedHomotopy κ x₀ (t • c) (s, y) = 0 →
        LinearMap.det (partialFDeriv (N.perturbedHomotopy κ x₀ (t • c)) (s, y)).toLinearMap ≠ 0)
    (hfinH : ∀ (t s : ℝ), 0 ≤ s → s ≤ 1 →
        ((fun y => N.perturbedHomotopy κ x₀ (t • c) (s, y)) ⁻¹' {0} ∩
          N.positiveClassRegion x₀).Finite) :
    ∀ᶠ t in 𝓝 (0 : ℝ), ∃ z₁ z₂ : ClassCoord N, z₁ ≠ z₂ ∧
      z₁ ∈ N.positiveClassRegion x₀ ∧ z₂ ∈ N.positiveClassRegion x₀ ∧
      N.perturbedSteadyStateMap κ x₀ (t • c) z₁ = 0 ∧
      N.perturbedSteadyStateMap κ x₀ (t • c) z₂ = 0 ∧
      ((SignType.sign (N.reducedJacobian κ x₀ z₁).det : SignType) : ℤ) =
        ((SignType.sign (N.reducedJacobian κ x₀ ystar).det : SignType) : ℤ) := by
  -- the perturbation creates a zero near `ystar`
  have hV₀ : N.positiveClassRegion x₀ ∈ 𝓝 ystar :=
    (N.isOpen_positiveClassRegion x₀).mem_nhds hystar
  obtain ⟨V, hVV₀, hVopen, hystarV, hev⟩ :=
    N.exists_perturbed_zero_near_of_det_ne_zero κ x₀ c ystar hzero hdet hV₀
  -- the finiteness of the zero set of the perturbed map, for each parameter
  have hfinQ : ∀ t : ℝ, (N.perturbedSteadyStateMap κ x₀ (t • c) ⁻¹' {0} ∩
      N.positiveClassRegion x₀).Finite := by
    intro t
    have hpre : (fun y => N.perturbedHomotopy κ x₀ (t • c) (1, y)) ⁻¹' {0}
        = N.perturbedSteadyStateMap κ x₀ (t • c) ⁻¹' {0} := by
      have h := N.perturbedSteadyStateMap_preimage_eq κ x₀ (t • c) 1
      rwa [one_smul] at h
    rw [← hpre]
    exact hfinH t 1 (by norm_num : (0 ≤ (1 : ℝ))) (by norm_num : (1 ≤ (1 : ℝ)))
  -- the relative degree of the perturbed map is the class degree
  have hdegP : ∀ t : ℝ, localDegreeOn (N.perturbedSteadyStateMap κ x₀ (t • c)) 0
      (N.positiveClassRegion x₀) (hfinQ t) = N.positiveClassDegree κ x₀ hfin := by
    intro t
    have hbd' : ∀ t' ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ closure (N.positiveClassRegion x₀),
        N.perturbedHomotopy κ x₀ (t • c) (t', y) = 0 → y ∈ N.positiveClassRegion x₀ := by
      intro t' ht' y hy hz
      exact hbdH t t' ht'.1 ht'.2 y hy hz
    have hreg' : ∀ t' ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ N.positiveClassRegion x₀,
        N.perturbedHomotopy κ x₀ (t • c) (t', y) = 0 →
        LinearMap.det (partialFDeriv (N.perturbedHomotopy κ x₀ (t • c)) (t', y)).toLinearMap ≠ 0 := by
      intro t' ht' y hy hz
      exact hregH t t' ht'.1 ht'.2 y hy hz
    have hfin' : ∀ t' ∈ Set.Icc (0 : ℝ) 1,
        ((fun y => N.perturbedHomotopy κ x₀ (t • c) (t', y)) ⁻¹' {0} ∩
          N.positiveClassRegion x₀).Finite := by
      intro t' ht'
      exact hfinH t t' ht'.1 ht'.2
    have hdeg := N.positiveClassDegree_eq_degree_perturbed κ x₀ (t • c) hUcpt hbd' hreg' hfin'
      hfin (hfinQ t)
    exact hdeg.symm
  filter_upwards [hev] with t ht
  obtain ⟨z₁, hz₁V, hz₁zero, hz₁sign⟩ := ht
  have hz₁reg : z₁ ∈ N.positiveClassRegion x₀ := hVV₀ hz₁V
  -- the local degree of the perturbed map at `z₁` is the one of the unperturbed map at `ystar`
  have hz₁local : ((SignType.sign (LinearMap.det
      (fderiv ℝ (N.perturbedSteadyStateMap κ x₀ (t • c)) z₁).toLinearMap) : SignType) : ℤ)
      = -(N.positiveClassDegree κ x₀ hfin) := by
    rw [N.det_fderiv_perturbedSteadyStateMap_eq_reducedJacobian_det]
    rw [hz₁sign]
    exact hlocal
  -- the counting step for the perturbed map
  have hdegQ : localDegreeOn (N.perturbedSteadyStateMap κ x₀ (t • c)) 0
      (N.positiveClassRegion x₀) (hfinQ t) ≠ 0 := by
    rw [hdegP t]
    exact hdeg
  have hz₁local' : ((SignType.sign (LinearMap.det
      (fderiv ℝ (N.perturbedSteadyStateMap κ x₀ (t • c)) z₁).toLinearMap) : SignType) : ℤ)
      = -(localDegreeOn (N.perturbedSteadyStateMap κ x₀ (t • c)) 0
        (N.positiveClassRegion x₀) (hfinQ t)) := by
    rw [hdegP t]
    exact hz₁local
  have hz₂ : ∃ z₂ ∈ N.positiveClassRegion x₀,
      N.perturbedSteadyStateMap κ x₀ (t • c) z₂ = 0 ∧ z₂ ≠ z₁ := by
    obtain ⟨z₂, hz₂reg, hz₂zero, hz₂ne⟩ :=
      exists_other_zero_of_localDegreeOn_neg (N.perturbedSteadyStateMap κ x₀ (t • c))
        (U := N.positiveClassRegion x₀) (hfinQ t) hdegQ z₁ hz₁reg hz₁zero hz₁local'
    exact ⟨z₂, hz₂reg, hz₂zero, hz₂ne⟩
  obtain ⟨z₂, hz₂reg, hz₂zero, hz₂ne⟩ := hz₂
  refine ⟨z₁, z₂, hz₂ne.symm, hz₁reg, hz₂reg, ?_, hz₂zero, hz₁sign⟩
  rw [N.perturbedSteadyStateMap_eq_perturbedHomotopy_slice]
  exact hz₁zero

/-! ## A consistency check on the concrete two-species instance -/

namespace DegreeExampleCheck

open DegreeExample

/-- **The class degree of the two-species example is `(-1)^s`.**  This is the *total-degree*
hypothesis of the Conradi–Feliu–Mincheva–Wiuf theorem: for the fully open two-species network
(`s = 2`) the relative degree of the reduced field on the nonnegative class is `1 = (-1)^2`.  The
hypothesis is thus satisfied in this instance. -/
theorem classDegree_eq_pow_neg_one_stoichRank :
    N.nonnegativeClassDegree rates 0 hfinN = (-1 : ℤ) ^ N.stoichRank := by
  rw [DegreeExampleCheck.classDegree_eq_one, DegreeExample.stoichRank_eq]
  norm_num

/-- **The unique steady state of the two-species example does not carry the exceptional sign.**
The reduced Jacobian determinant at the unique steady state `b` is `1 > 0`, so its local degree is
`+1`, while the class degree is `+1` as well: the local degree is *not* the opposite of the class
degree, and the Conradi–Feliu–Mincheva–Wiuf conclusion does not apply (as it should not: this
network has a unique steady state). -/
theorem localDegree_ne_neg_classDegree :
    ((SignType.sign (N.reducedJacobian rates 0 b).det : SignType) : ℤ)
      ≠ -(N.nonnegativeClassDegree rates 0 hfinN) := by
  have h1 : ((SignType.sign (N.reducedJacobian rates 0 b).det : SignType) : ℤ) = 1 := by
    rw [DegreeExampleCheck.reducedJacobian_det_at_b]
    rw [sign_pos (by norm_num : (0 : ℝ) < 1)]
    rfl
  have h2 : N.nonnegativeClassDegree rates 0 hfinN = 1 := DegreeExampleCheck.classDegree_eq_one
  rw [h1, h2]
  norm_num

end DegreeExampleCheck

end Network

end CRNT


