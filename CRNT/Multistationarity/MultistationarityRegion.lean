import CRNT.Multistationarity.RankOneParameterRegion
import CRNT.Multistationarity.ReducedJacobian
import CRNT.Multistationarity.ReducedJacobianSign
import CRNT.Multistationarity.MultistationarityRegionOpen
import CRNT.Examples.AugmentedCellsInstance

/-!
# Parameter regions for multistationarity: the rank-one case

This module supplies the *explicit* description of the multistationarity regions of field-map
leaf **M13** ("Parameter regions for multistationarity"), completing the part that was missing:
the **reduced-determinant (circuit) description** of the regions, in the rank-one case
`S(N) = span {v}` singled out by Conradi–Feliu–Mincheva–Wiuf.

## The Conradi–Feliu–Mincheva–Wiuf picture

Fix a network `N` of rank one, `S(N) = span {v}` with `v ≠ 0`, a positive class representative
`x₀`, and a coordinate `i₀` with `v i₀ ≠ 0`.  The compatibility class of `x₀` is the segment
`{x₀ + t • v}`; the mass-action field on it is `φ(t) • v` with

`φ(t) = (N.massActionVectorField κ (x₀ + t • v)) i₀ / v i₀`   (`Network.lineField`),

the *scalar field* of the network along the class.  A point `x₀ + t • v` is a steady state exactly
when `φ(t) = 0` (`Network.isMassActionSteadyState_line_iff`), and the **reduced derivative**
`φ'(t)` is the scalar that decides uniqueness versus multistationarity: if `φ' < 0` at every
positive steady state of the class there is exactly one, while `φ' > 0` at one of them forces at
least three (`Network.rankOne_existsUnique_of_deriv_neg`,
`Network.rankOne_three_steadyStates_of_deriv_pos`, `Network.rankOne_multistationary_iff`).

## The reduced determinant

`Network.reducedJacobian` is the `s × s` Jacobian of the mass-action field restricted to the
stoichiometric subspace, read in a chart of that subspace (`Network.reducedJacobian`,
`Network.reducedJacobian_eq_mul`).  For rank one it is a `1 × 1` matrix, and *its determinant is
the reduced derivative*:

* `massActionMonomial_hasDerivAt_along` — the directional derivative of a source monomial along
  the class line is the gradient of the monomial paired with the direction;
* `massActionJacobianCLM_alongLine` — the mass-action Jacobian applied to `v` is the reduced
  derivative times `v`: the analytic heart of the identification;
* `reducedJacobian_det_eq_deriv` — the determinant of the reduced Jacobian at the chart
  coordinate of a class point is the reduced derivative `φ'(t)`;
* `reducedJacobian_det_sign_iff` — the sign form of the same statement: the sign of the reduced
  determinant is the sign of `φ'`, i.e. the Conradi–Feliu–Mincheva–Wiuf sign condition that
  separates uniqueness from multistationarity.

The chart-free version of the reduced determinant — the determinant of the Jacobian restricted to
the one-dimensional stoichiometric subspace, read in the basis `{v}` — is `Network.rankOneReducedDet`;
`rankOne_reducedDet_eq_deriv` and `rankOne_reducedDet_sign_iff` identify it with the reduced
derivative as well.

Consequently the **multistationarity region of a rank-one network is the set of parameters for
which the reduced determinant is positive at some positive steady state of the class**
(`rankOne_multistationary_iff_det_pos`): this is the explicit description of the region that
leaf M13 was missing.  `rankOne_isNondegenerateSteadyState_iff` records the accompanying
hypothesis of the theorem — every steady state of the class is nondegenerate — as the
non-vanishing of the reduced derivative.

## The circuit reading

For a rank-one network every reaction vector is a multiple of `v`; write `reactionVector r =
c_r v`.  The *signed rate* `κ_r c_r` collects the rate constant with the orientation of the
reaction along `v`.  The scalar field of the network along the class is the sum of the signed
rates weighted by the source monomials (`lineField_eq_sum_signedRates`), and the reduced
determinant is the sum of the signed rates weighted by the directional derivatives of the source
monomials (`reducedDet_eq_sum_signedRates`); its sign is therefore governed by the orientations of
the reaction vectors along the single stoichiometric direction.  A network whose reaction
vectors all point the same way along `v` is the rank-one analogue of a *positive circuit*, and it
carries no positive steady state at all (`rankOne_noPositiveCircuit_noSteadyState`).

## The parameter region

`MultistationarityRegion` collects the parameters `(κ, T)` (rate constants and totals) for which
the class `{x | L x = T}` carries two distinct nondegenerate positive steady states.  It is open
(`isOpen_multistationarityRegion`, reusing the implicit function theorem of
`Network.isOpen_nondegRegion`) and nonempty for the rank-one network `X ⇌ Y`, `2X + Y → 3X`,
`X + 2Y → 3Y` (`multistationarityRegion_nonempty_augmentedCells`).  The variant in the "rate
constants and class representative" parameterization is `ClassMultistationarityRegion`; it is not
open in its second coordinate (the class of a representative is a coset of the stoichiometric
subspace), and the open region is the one in the totals parameterization.

## A concrete instance

`instNet` is the rank-one network `X ⇌ Y`, `2X + Y → 3X`, `X + 2Y → 3Y` with the rate constants
`instκ = (3, 3, 16, 16)`.  Its stoichiometric subspace is the line spanned by `instV = X − Y`
(`instNet_stoichSubspace`), the scalar field along the class `{x | x_X + x_Y = 1}` is
`φ(t) = 2t − 32t³` (`instLineField`, `instLineField_deriv`), and the class carries three positive
steady states — at `t = −1/4, 0, 1/4` — with reduced determinants `−4`, `2`, `−4`
(`inst_steadyState`).  The middle steady state has a *positive* reduced determinant, which is
the Conradi–Feliu–Mincheva–Wiuf signature of a multistationary class (`inst_multistationary`).

## Relation to leaf M9 (Brouwer degree)

The degree machinery of M9 gives *existence* of a steady state on a compact class without
boundary steady state (`Network.rankOne_exists_positive_steadyState`); the determinant
description above adds the *uniqueness versus multistationarity* alternative of
Conradi–Feliu–Mincheva–Wiuf, which in rank one is read off the sign of a single scalar — the
reduced determinant — rather than from a Brouwer degree in dimension `s ≥ 2`.

Depends on: `CRNT.Multistationarity.RankOneParameterRegion`,
`CRNT.Multistationarity.ReducedJacobian`, `CRNT.Multistationarity.ReducedJacobianSign`,
`CRNT.Multistationarity.MultistationarityRegionOpen`, `CRNT.Examples.AugmentedCellsInstance`.
-/

namespace CRNT

namespace Network

open Filter Topology Set

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ## The scalar field and the Jacobian along the class -/

/-- **The derivative of the source monomial along the class line.**  The source monomial
`∏ s, x s ^ y s` is a product of powers of the affine coordinates `x₀ s + t v s`; the product rule
gives the directional derivative as the sum of the partial derivatives, which are exactly the
entries of the source-monomial gradient `massActionMonomialGrad`. -/
theorem massActionMonomial_hasDerivAt_along (y : Complex S) (x₀ v : Concentration S) (t : ℝ) :
    HasDerivAt (fun s : ℝ => y.massActionMonomial (x₀ + s • v))
      (∑ j, massActionMonomialGrad y (x₀ + t • v) j * v j) t := by
  classical
  have hmono : (fun s : ℝ => y.massActionMonomial (x₀ + s • v))
      = fun s => ∏ j, (x₀ j + s * v j) ^ (y j) := by
    funext s
    simp [Complex.massActionMonomial, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hfactor : ∀ j ∈ (Finset.univ : Finset S),
      HasDerivAt (fun s : ℝ => (x₀ j + s * v j) ^ (y j))
        ((y j : ℝ) * (x₀ j + t * v j) ^ (y j - 1) * v j) t := by
    intro j hj
    have hlin : HasDerivAt (fun s : ℝ => x₀ j + s * v j) (v j) t := by
      have h1 : HasDerivAt (fun s : ℝ => s * v j) (1 * v j) t :=
        (hasDerivAt_id t).mul_const (v j)
      have h2 := h1.const_add (x₀ j)
      simpa using h2
    have hpow := hlin.pow (y j)
    have hpowfun : ((fun s => x₀ j + s * v j) ^ y j) = fun s => (x₀ j + s * v j) ^ (y j) := by
      funext s
      exact Pi.pow_apply _ _ s
    simpa only [hpowfun] using hpow
  have h := HasDerivAt.finsetProd (u := (Finset.univ : Finset S)) (𝕜 := ℝ) (𝔸' := ℝ)
      (f := fun j s => (x₀ j + s * v j) ^ (y j))
      (f' := fun j => (y j : ℝ) * (x₀ j + t * v j) ^ (y j - 1) * v j) (x := t)
      (fun j hj => hfactor j hj)
  have hfun : (∏ j, fun s => (x₀ j + s * v j) ^ (y j))
      = fun s => ∏ j, (x₀ j + s * v j) ^ (y j) := by
    funext s
    simp
  have hprod : HasDerivAt (fun s : ℝ => ∏ j, (x₀ j + s * v j) ^ (y j))
      (∑ j, ((∏ k ∈ (Finset.univ.erase j), (x₀ k + t * v k) ^ (y k)) *
        ((y j : ℝ) * (x₀ j + t * v j) ^ (y j - 1) * v j))) t := by
    simpa [hfun, smul_eq_mul, mul_assoc] using h
  have heq : (∑ j, ((∏ k ∈ (Finset.univ.erase j), (x₀ k + t * v k) ^ (y k)) *
        ((y j : ℝ) * (x₀ j + t * v j) ^ (y j - 1) * v j)))
      = ∑ j, massActionMonomialGrad y (x₀ + t • v) j * v j := by
    refine Finset.sum_congr (M := ℝ) rfl fun j _ => ?_
    have hx : ∀ k, x₀ k + t * v k = (x₀ + t • v) k := by
      intro k
      simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    simp only [massActionMonomialGrad]
    have h1 : (∏ k ∈ (Finset.univ.erase j), (x₀ k + t * v k) ^ (y k))
        = ∏ k ∈ (Finset.univ.erase j), ((x₀ + t • v) k) ^ (y k) := by
      refine Finset.prod_congr (M := ℝ) rfl fun k hk => ?_
      rw [hx k]
    rw [h1]
    have h2 : (x₀ j + t * v j) ^ (y j - 1) = ((x₀ + t • v) j) ^ (y j - 1) := by
      rw [hx j]
    rw [h2]
    ring
  rw [heq] at hprod
  rw [hmono]
  exact hprod

/-- **The mass-action Jacobian along the class line is the reduced derivative.**  For a rank-one
network (`S(N) = span {v}`) the mass-action Jacobian applied to the direction `v` is `φ'(t) • v`,
where `φ` is the scalar field of the network along the class.  This is the analytic core of the
Conradi–Feliu–Mincheva–Wiuf identification of the reduced determinant with the derivative of the
scalar field. -/
theorem massActionJacobianCLM_alongLine (N : Network S) (κ : N.RateConstants) {v : Concentration S}
    (hspan : N.stoichSubspace = Submodule.span ℝ {v}) {i₀ : S} (hi₀ : v i₀ ≠ 0)
    (x₀ : Concentration S) (t : ℝ) :
    ∀ s, (N.massActionJacobianCLM κ (x₀ + t • v) v) s
      = (deriv (N.lineField κ x₀ v i₀) t) * v s := by
  classical
  -- every reaction vector is a multiple of `v`
  have hmul : ∀ r, N.reactionVector r = ((N.reactionVector r) i₀ / v i₀) • v := by
    intro r
    have hmem : N.reactionVector r ∈ N.stoichSubspace := N.reactionVector_mem_stoichSubspace r
    rw [hspan] at hmem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    refine hc.symm.trans ?_
    have hci : c * v i₀ = N.reactionVector r i₀ := by
      have h := congrFun hc i₀
      simpa [Pi.smul_apply, smul_eq_mul] using h
    have hcoeff : c = N.reactionVector r i₀ / v i₀ := by
      rw [eq_div_iff (hi₀)]
      linarith
    rw [hcoeff]
  have hmul' : ∀ r s, N.reactionVector r s = ((N.reactionVector r) i₀ / v i₀) * v s := by
    intro r s
    have h := congrFun (hmul r) s
    simpa [Pi.smul_apply, smul_eq_mul] using h
  -- the scalar field along the class
  have hφ : ∀ u, N.lineField κ x₀ v i₀ u
      = ∑ r, κ.k r * ((N.reactionVector r) i₀ / v i₀) *
          (N.reaction r).source.massActionMonomial (x₀ + u • v) := by
    intro u
    have hlf : N.lineField κ x₀ v i₀ u
        = N.massActionVectorField κ (x₀ + u • v) i₀ / v i₀ := rfl
    rw [hlf, massActionVectorField_apply, Finset.sum_div]
    refine Finset.sum_congr (M := ℝ) rfl fun r _ => ?_
    have hrate : N.massActionRate κ r (x₀ + u • v)
        = κ.k r * (N.reaction r).source.massActionMonomial (x₀ + u • v) := rfl
    rw [hrate]
    field_simp
  -- the derivative of the scalar field
  have hφderiv : deriv (fun u : ℝ => N.lineField κ x₀ v i₀ u) t
      = ∑ r, κ.k r * ((N.reactionVector r) i₀ / v i₀) *
        (∑ j, massActionMonomialGrad (N.reaction r).source (x₀ + t • v) j * v j) := by
    have hfun : (fun u : ℝ => N.lineField κ x₀ v i₀ u)
        = fun u => ∑ r, κ.k r * ((N.reactionVector r) i₀ / v i₀) *
            (N.reaction r).source.massActionMonomial (x₀ + u • v) := by
      funext u
      exact hφ u
    rw [hfun]
    have hsum : HasDerivAt (fun u : ℝ => ∑ r, κ.k r * ((N.reactionVector r) i₀ / v i₀) *
          (N.reaction r).source.massActionMonomial (x₀ + u • v))
        (∑ r, κ.k r * ((N.reactionVector r) i₀ / v i₀) *
          (∑ j, massActionMonomialGrad (N.reaction r).source (x₀ + t • v) j * v j)) t := by
      refine HasDerivAt.fun_sum (u := (Finset.univ : Finset N.R)) ?_
      intro r hr
      have h := massActionMonomial_hasDerivAt_along (N.reaction r).source x₀ v t
      exact h.const_mul (κ.k r * ((N.reactionVector r) i₀ / v i₀))
    exact hsum.deriv
  -- the Jacobian along the class
  intro s
  rw [N.massActionJacobianCLM_apply]
  have hexp : ((N.massActionJacobian κ (x₀ + t • v)).mulVec v) s
      = ∑ r : N.R, κ.k r * ((N.reactionVector r) i₀ / v i₀) *
          (∑ j : S, massActionMonomialGrad (N.reaction r).source (x₀ + t • v) j * v j) * v s := by
    simp only [Matrix.mulVec_apply_eq_sum]
    have hM : ∀ j : S, (N.massActionJacobian κ (x₀ + t • v)) s j
        = ∑ r : N.R, κ.k r * massActionMonomialGrad (N.reaction r).source (x₀ + t • v) j *
            N.reactionVector r s := by
      intro j
      rfl
    have hexp2 : (∑ j : S, (N.massActionJacobian κ (x₀ + t • v)) s j * v j)
        = ∑ j : S, (∑ r : N.R, κ.k r * massActionMonomialGrad (N.reaction r).source (x₀ + t • v) j *
            N.reactionVector r s) * v j := by
      refine Finset.sum_congr (M := ℝ) rfl fun j _ => ?_
      rw [hM j]
    rw [hexp2]
    calc (∑ j : S, (∑ r : N.R, κ.k r * massActionMonomialGrad (N.reaction r).source (x₀ + t • v) j *
          N.reactionVector r s) * v j)
        = ∑ j : S, ∑ r : N.R, (κ.k r * massActionMonomialGrad (N.reaction r).source (x₀ + t • v) j *
          N.reactionVector r s) * v j := by
            refine Finset.sum_congr (M := ℝ) rfl fun j _ => ?_
            rw [Finset.sum_mul]
      _ = ∑ r : N.R, ∑ j : S, (κ.k r * massActionMonomialGrad (N.reaction r).source (x₀ + t • v) j *
          N.reactionVector r s) * v j := by
            exact Finset.sum_comm (β := ℝ) (γ := S) (α := N.R)
              (s := (Finset.univ : Finset S)) (t := (Finset.univ : Finset N.R))
              (f := fun j r => (κ.k r * massActionMonomialGrad (N.reaction r).source (x₀ + t • v) j *
                N.reactionVector r s) * v j)
      _ = ∑ r : N.R, (κ.k r * N.reactionVector r s) *
          (∑ j : S, massActionMonomialGrad (N.reaction r).source (x₀ + t • v) j * v j) := by
            refine Finset.sum_congr (M := ℝ) rfl fun r _ => ?_
            calc (∑ j : S, (κ.k r * massActionMonomialGrad (N.reaction r).source (x₀ + t • v) j *
                  N.reactionVector r s) * v j)
                = ∑ j : S, (κ.k r * N.reactionVector r s) *
                  (massActionMonomialGrad (N.reaction r).source (x₀ + t • v) j * v j) := by
                    refine Finset.sum_congr (M := ℝ) rfl fun j _ => ?_
                    ring
              _ = (κ.k r * N.reactionVector r s) *
                  (∑ j : S, massActionMonomialGrad (N.reaction r).source (x₀ + t • v) j * v j) := by
                    rw [← Finset.mul_sum]
      _ = ∑ r : N.R, κ.k r * ((N.reactionVector r) i₀ / v i₀) *
          (∑ j : S, massActionMonomialGrad (N.reaction r).source (x₀ + t • v) j * v j) * v s := by
            refine Finset.sum_congr (M := ℝ) rfl fun r _ => ?_
            rw [hmul' r]
            ring
  rw [hexp, hφderiv]
  have hlast : (∑ r : N.R, (κ.k r * ((N.reactionVector r) i₀ / v i₀) *
        (∑ j : S, massActionMonomialGrad (N.reaction r).source (x₀ + t • v) j * v j)) * v s)
      = (∑ r : N.R, κ.k r * ((N.reactionVector r) i₀ / v i₀) *
        (∑ j : S, massActionMonomialGrad (N.reaction r).source (x₀ + t • v) j * v j)) * v s := by
    rw [← Finset.sum_mul]
  rw [hlast]

/-! ## The reduced determinant of a rank-one network -/

/-- **The rank-one reduced determinant.**  For a rank-one network the mass-action Jacobian
restricted to the one-dimensional stoichiometric subspace `span {v}` is the multiplication by a
scalar; that scalar is the determinant of the restriction, and it is read off at the coordinate
`i₀` with `v i₀ ≠ 0`. -/
noncomputable def rankOneReducedDet (N : Network S) (κ : N.RateConstants) (v : Concentration S)
    (i₀ : S) (x : Concentration S) : ℝ :=
  ((N.massActionJacobianCLM κ x) v) i₀ / v i₀

/-- **The determinant of a `1 × 1` matrix is its single entry.** -/
theorem det_eq_entry_of_card_one {n : ℕ} (h : n = 1) {i : Fin n} (hi : i.val = 0)
    (M : Matrix (Fin n) (Fin n) ℝ) : M.det = M i i := by
  classical
  have hine : (⟨0, by rw [h]; norm_num⟩ : Fin n) = i := by
    ext
    exact hi.symm
  let e : Fin n ≃ Fin 1 :=
    { toFun := fun j => ⟨j.val, by omega⟩
      invFun := fun j => ⟨j.val, by omega⟩
      left_inv := by intro j; ext; rfl
      right_inv := by intro j; ext; rfl }
  have h1 := Matrix.det_reindex_self e M
  rw [Matrix.det_fin_one] at h1
  have h2 : (M.reindex e e) 0 0 = M i i := by
    rw [Matrix.reindex_apply, Matrix.submatrix_apply]
    have he : e.symm 0 = (⟨0, by rw [h]; norm_num⟩ : Fin n) := by rfl
    rw [he, ← hine]
  rw [← h1, h2]

/-- **The stoichiometric rank of a rank-one network is one.** -/
theorem stoichRank_eq_one_of_span (N : Network S) {v : Concentration S}
    (hspan : N.stoichSubspace = Submodule.span ℝ {v}) (hne : v ≠ 0) :
    N.stoichRank = 1 := by
  rw [show N.stoichRank = Module.finrank ℝ N.stoichSubspace from rfl, hspan,
    finrank_span_singleton hne]

/-- **The reduced Jacobian determinant is the reduced derivative.**  For a rank-one network the
determinant of the reduced Jacobian `1 × 1` matrix, evaluated at the chart coordinate of the
class point `x₀ + t • v`, is the derivative `φ'(t)` of the scalar field along the class. -/
theorem reducedJacobian_det_eq_deriv (N : Network S) (κ : N.RateConstants) (hcard : N.stoichRank = 1)
    {v : Concentration S} (hspan : N.stoichSubspace = Submodule.span ℝ {v})
    {i₀ : S} (hi₀ : v i₀ ≠ 0) (x₀ : Concentration S) (t : ℝ) :
    Matrix.det (N.reducedJacobian κ x₀ (N.chartCoord x₀ (x₀ + t • v)))
      = deriv (N.lineField κ x₀ v i₀) t := by
  classical
  have hpos : 0 < N.stoichRank := by rw [hcard]; norm_num
  set i : Fin N.stoichRank := ⟨0, hpos⟩ with hi
  set e₀ : Fin N.stoichRank → ℝ := Pi.single i 1 with he₀
  -- the chart's basis vector is a nonzero multiple of `v`
  have hmem' : N.stoichChart e₀ ∈ Submodule.span ℝ {v} := by
    rw [← hspan]; exact N.stoichChart_mem e₀
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem'
  have he₀ne : (Pi.single i 1 : Fin N.stoichRank → ℝ) ≠ 0 := by
    intro hz
    have hz' := congrFun hz i
    simp at hz'
  have hne0 : N.stoichChart e₀ ≠ 0 := by
    intro h
    have h1 : N.stoichChart e₀ = N.stoichChart 0 := by
      rw [h]
      exact (map_zero N.stoichChart).symm
    have h2 : e₀ = 0 := N.stoichChart_injective h1
    exact he₀ne (he₀ ▸ h2)
  have hcne : c ≠ 0 := by
    intro hc0
    have : N.stoichChart e₀ = 0 := by rw [← hc, hc0, zero_smul]
    exact hne0 this
  -- the projection of the basis vector
  have hproj : N.stoichProj (N.stoichChart e₀) = e₀ := N.stoichProj_stoichChart e₀
  -- the chart coordinate of the class point
  have hchart : N.affineChart x₀ (N.chartCoord x₀ (x₀ + t • v)) = x₀ + t • v :=
    N.affineChart_chartCoord (N.stoichCompatible_line hspan x₀ t)
  -- the entry of the reduced Jacobian
  have hentry : N.reducedJacobian κ x₀ (N.chartCoord x₀ (x₀ + t • v)) i i
      = N.stoichProj (N.massActionJacobianCLM κ (x₀ + t • v) (N.stoichChart e₀)) i := by
    have h1 : N.reducedJacobian κ x₀ (N.chartCoord x₀ (x₀ + t • v))
        = jacobianMatrix (N.reducedJacobianCLM κ x₀ (N.chartCoord x₀ (x₀ + t • v))) := rfl
    have h2 : N.reducedJacobianCLM κ x₀ (N.chartCoord x₀ (x₀ + t • v))
        = N.stoichProj.comp
          ((N.massActionJacobianCLM κ (N.affineChart x₀ (N.chartCoord x₀ (x₀ + t • v)))).comp
            N.stoichChart) := rfl
    rw [h1, jacobianMatrix, LinearMap.toMatrix'_apply, h2]
    rw [hchart, he₀]
    rfl
  -- the Jacobian along the class
  have hJ : ∀ s, (N.massActionJacobianCLM κ (x₀ + t • v) v) s
      = (deriv (N.lineField κ x₀ v i₀) t) * v s :=
    massActionJacobianCLM_alongLine N κ hspan hi₀ x₀ t
  -- the projection of `v`
  have hprojv : N.stoichProj v = (c⁻¹) • e₀ := by
    have h1 : N.stoichProj (c • v) = c • (N.stoichProj v) := map_smul N.stoichProj c v
    have h1' : N.stoichProj (c • v) = N.stoichProj (N.stoichChart e₀) := by rw [hc]
    have h2 : c • (N.stoichProj v) = e₀ := by
      rw [← h1]
      exact h1'.trans hproj
    have h3 : c⁻¹ • (c • N.stoichProj v) = c⁻¹ • e₀ := by rw [h2]
    rw [smul_smul, inv_mul_cancel₀ (hcne), one_smul] at h3
    exact h3
  -- the entry
  have hfinal : N.stoichProj (N.massActionJacobianCLM κ (x₀ + t • v) (N.stoichChart e₀)) i
      = deriv (N.lineField κ x₀ v i₀) t := by
    have h1 : N.massActionJacobianCLM κ (x₀ + t • v) (N.stoichChart e₀)
        = N.massActionJacobianCLM κ (x₀ + t • v) (c • v) := by rw [hc]
    rw [h1]
    have h2 := map_smul (N.massActionJacobianCLM κ (x₀ + t • v)) c v
    rw [h2]
    have h6 : N.stoichProj (N.massActionJacobianCLM κ (x₀ + t • v) v)
        = (deriv (N.lineField κ x₀ v i₀) t) • (N.stoichProj v) := by
      have hx : N.massActionJacobianCLM κ (x₀ + t • v) v
          = (deriv (N.lineField κ x₀ v i₀) t) • v := by
        funext s
        simp only [Pi.smul_apply, smul_eq_mul]
        exact hJ s
      rw [hx]
      exact map_smul N.stoichProj _ v
    have h4 : N.stoichProj (c • (N.massActionJacobianCLM κ (x₀ + t • v) v))
        = c • (N.stoichProj (N.massActionJacobianCLM κ (x₀ + t • v) v)) :=
      map_smul N.stoichProj c _
    rw [h4, h6]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hprojv]
    simp only [Pi.smul_apply, smul_eq_mul]
    have he₀i : e₀ i = 1 := by
      simp [he₀]
    rw [he₀i]
    field_simp
  -- the determinant
  have hdet : (N.reducedJacobian κ x₀ (N.chartCoord x₀ (x₀ + t • v))).det
      = N.reducedJacobian κ x₀ (N.chartCoord x₀ (x₀ + t • v)) i i :=
    det_eq_entry_of_card_one hcard rfl _
  rw [hdet, hentry]
  exact hfinal

/-! ## The rank-one reduced determinant as a reduced derivative -/

/-- **The rank-one reduced determinant is the reduced derivative.**  The reduced determinant of a
rank-one network — the determinant of the mass-action Jacobian restricted to the one-dimensional
stoichiometric subspace — is the derivative of the scalar field along the class. -/
theorem rankOne_reducedDet_eq_deriv (N : Network S) (κ : N.RateConstants) {v : Concentration S}
    (hspan : N.stoichSubspace = Submodule.span ℝ {v}) {i₀ : S} (hi₀ : v i₀ ≠ 0)
    (x₀ : Concentration S) (t : ℝ) :
    rankOneReducedDet N κ v i₀ (x₀ + t • v) = deriv (N.lineField κ x₀ v i₀) t := by
  unfold rankOneReducedDet
  have hJ := massActionJacobianCLM_alongLine N κ hspan hi₀ x₀ t
  have hJi := hJ i₀
  rw [hJi]
  field_simp

/-- **The sign form of the reduced-determinant identification.**  The sign of the reduced
determinant at a class point is the sign of the reduced derivative, i.e. of the Conradi–Feliu–
Mincheva–Wiuf sign condition that separates uniqueness from multistationarity. -/
theorem reducedJacobian_det_sign_iff (N : Network S) (κ : N.RateConstants) (hcard : N.stoichRank = 1)
    {v : Concentration S} (hspan : N.stoichSubspace = Submodule.span ℝ {v})
    {i₀ : S} (hi₀ : v i₀ ≠ 0) (x₀ : Concentration S) (t : ℝ) :
    (0 < (N.reducedJacobian κ x₀ (N.chartCoord x₀ (x₀ + t • v))).det) ↔
      0 < deriv (N.lineField κ x₀ v i₀) t := by
  rw [reducedJacobian_det_eq_deriv N κ hcard hspan hi₀ x₀ t]

/-- **The sign form for the chart-free reduced determinant.** -/
theorem rankOne_reducedDet_sign_iff (N : Network S) (κ : N.RateConstants) {v : Concentration S}
    (hspan : N.stoichSubspace = Submodule.span ℝ {v}) {i₀ : S} (hi₀ : v i₀ ≠ 0)
    (x₀ : Concentration S) (t : ℝ) :
    (0 < rankOneReducedDet N κ v i₀ (x₀ + t • v)) ↔ 0 < deriv (N.lineField κ x₀ v i₀) t := by
  rw [rankOne_reducedDet_eq_deriv N κ hspan hi₀ x₀ t]

/-! ## The multistationarity region in terms of the reduced determinant -/

section RankOne

variable (N : Network S) (κ : RateConstants N) {x₀ v : Concentration S}
  (hspan : N.stoichSubspace = Submodule.span ℝ {v})
  (hP : (Finset.univ.filter fun s => 0 < v s).Nonempty)
  (hQ : (Finset.univ.filter fun s => v s < 0).Nonempty)
  (hx : x₀.Positive)
  (hbd : ∀ x, N.StoichCompatible x₀ x → x.Nonnegative → ¬ x.Positive →
    ¬ N.IsMassActionSteadyState κ x)
  {i₀ : S} (hi₀ : v i₀ ≠ 0)

include hspan hx hbd hi₀

/-- **The multistationarity region of a rank-one network, in terms of the reduced determinant.**
For a rank-one network whose class carries only nondegenerate steady states, the class is
multistationary if and only if the reduced determinant is *positive* at one of its positive steady
states.  This is the explicit description of the region of leaf M13: the region consists of those
parameters for which the reduced determinant is positive somewhere on the class. -/
theorem rankOne_multistationary_iff_det_pos
    (hnd : ∀ t, lineLeft x₀ v hP < t → t < lineRight x₀ v hQ → N.lineField κ x₀ v i₀ t = 0 →
      deriv (N.lineField κ x₀ v i₀) t ≠ 0) :
    (∃ x y, x ≠ y ∧ N.StoichCompatible x₀ x ∧ x.Positive ∧ N.IsMassActionSteadyState κ x ∧
        N.StoichCompatible x₀ y ∧ y.Positive ∧ N.IsMassActionSteadyState κ y) ↔
      ∃ x, N.StoichCompatible x₀ x ∧ x.Positive ∧ N.IsMassActionSteadyState κ x ∧
        0 < rankOneReducedDet N κ v i₀ x := by
  rw [N.rankOne_multistationary_iff κ hspan hP hQ hx hbd hi₀ hnd]
  constructor
  · rintro ⟨t, htl, htr, hz, hd⟩
    refine ⟨x₀ + t • v, N.stoichCompatible_line hspan x₀ t, ?_, ?_, ?_⟩
    · exact (line_positive_iff hP hQ hx t).mpr ⟨htl, htr⟩
    · exact (N.isMassActionSteadyState_line_iff κ hspan hi₀ x₀ t).mpr hz
    · rw [rankOne_reducedDet_eq_deriv N κ hspan hi₀ x₀ t]
      exact hd
  · rintro ⟨x, hxc, hxp, hxs, hd⟩
    obtain ⟨t, rfl⟩ := N.exists_line_of_stoichCompatible hspan hxc
    have hpos := (line_positive_iff hP hQ hx t).mp hxp
    have hz : N.lineField κ x₀ v i₀ t = 0 :=
      (N.isMassActionSteadyState_line_iff κ hspan hi₀ x₀ t).mp hxs
    refine ⟨t, hpos.1, hpos.2, hz, ?_⟩
    rw [← rankOne_reducedDet_eq_deriv N κ hspan hi₀ x₀ t]
    exact hd

end RankOne

/-- **Nondegeneracy is the non-vanishing of the reduced derivative.**  For a rank-one network a
steady state is nondegenerate — the mass-action Jacobian is injective on the stoichiometric
subspace — exactly when the reduced derivative does not vanish.  This is the rank-one instance of
the Conradi–Feliu–Mincheva–Wiuf hypothesis that all steady states of the class are
nondegenerate. -/
theorem rankOne_isNondegenerateSteadyState_iff (N : Network S) (κ : N.RateConstants)
    {v : Concentration S} (hspan : N.stoichSubspace = Submodule.span ℝ {v}) (hne : v ≠ 0)
    {i₀ : S} (hi₀ : v i₀ ≠ 0) (x₀ : Concentration S) (t : ℝ) :
    N.IsNondegenerateSteadyState κ (x₀ + t • v) ↔
      deriv (N.lineField κ x₀ v i₀) t ≠ 0 := by
  have hJv : N.massActionJacobianCLM κ (x₀ + t • v) v
      = (deriv (N.lineField κ x₀ v i₀) t) • v := by
    funext s
    have hJ := massActionJacobianCLM_alongLine N κ hspan hi₀ x₀ t
    rw [hJ s]
    simp [Pi.smul_apply, smul_eq_mul]
  have hmem : v ∈ N.stoichSubspace := by
    rw [hspan]
    exact Submodule.mem_span_singleton.mpr ⟨1, by simp⟩
  constructor
  · intro hnd hφ
    have h0 : N.massActionJacobianCLM κ (x₀ + t • v) v = 0 := by
      rw [hJv]
      funext s
      simp [hφ]
    exact absurd (hnd v hmem h0) hne
  · intro hφ u hu hu0
    have hu' : ∃ c : ℝ, c • v = u := by
      rw [hspan] at hu
      exact Submodule.mem_span_singleton.mp hu
    obtain ⟨c, hc⟩ := hu'
    have hc0 : c = 0 := by
      have h1 : c * (deriv (N.lineField κ x₀ v i₀) t) * v i₀ = 0 := by
        have hz := congrFun hu0 i₀
        rw [← hc, map_smul] at hz
        have hJ := massActionJacobianCLM_alongLine N κ hspan hi₀ x₀ t i₀
        simp only [Pi.smul_apply, smul_eq_mul] at hz hJ
        calc c * (deriv (N.lineField κ x₀ v i₀) t) * v i₀
            = c * ((N.massActionJacobianCLM κ (x₀ + t • v) v) i₀) := by rw [hJ]; ring
          _ = 0 := hz
      have h2 : c * (deriv (N.lineField κ x₀ v i₀) t) = 0 := by
        rcases mul_eq_zero.mp h1 with h1 | h1
        · exact h1
        · exact absurd h1 hi₀
      rcases mul_eq_zero.mp h2 with hc' | hφ'
      · exact hc'
      · exact absurd hφ' hφ
    rw [← hc, hc0, zero_smul]

/-! ## The circuit reading of the reduced determinant -/

/-- **The scalar field of a rank-one network is a sum of signed rates.**  Every reaction vector is
a multiple `c_r v` of the single stoichiometric direction, and the *signed rate* `κ_r c_r` collects
the rate constant with the orientation of the reaction along `v`.  The scalar field of the network
along the class is the sum of the signed rates weighted by the source monomials. -/
theorem lineField_eq_sum_signedRates (N : Network S) (κ : N.RateConstants) {v : Concentration S}
    (hspan : N.stoichSubspace = Submodule.span ℝ {v}) {i₀ : S} (hi₀ : v i₀ ≠ 0)
    (x₀ : Concentration S) (u : ℝ) :
    N.lineField κ x₀ v i₀ u
      = ∑ r, κ.k r * ((N.reactionVector r) i₀ / v i₀) *
          (N.reaction r).source.massActionMonomial (x₀ + u • v) := by
  classical
  have hmul : ∀ r, N.reactionVector r = ((N.reactionVector r) i₀ / v i₀) • v := by
    intro r
    have hmem : N.reactionVector r ∈ N.stoichSubspace := N.reactionVector_mem_stoichSubspace r
    rw [hspan] at hmem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    refine hc.symm.trans ?_
    have hci : c * v i₀ = N.reactionVector r i₀ := by
      have h := congrFun hc i₀
      simpa [Pi.smul_apply, smul_eq_mul] using h
    have hcoeff : c = N.reactionVector r i₀ / v i₀ := by
      rw [eq_div_iff (hi₀)]
      linarith
    rw [hcoeff]
  have hmul' : ∀ r s, N.reactionVector r s = ((N.reactionVector r) i₀ / v i₀) * v s := by
    intro r s
    have h := congrFun (hmul r) s
    simpa [Pi.smul_apply, smul_eq_mul] using h
  have hlf : N.lineField κ x₀ v i₀ u
      = N.massActionVectorField κ (x₀ + u • v) i₀ / v i₀ := rfl
  rw [hlf, massActionVectorField_apply, Finset.sum_div]
  refine Finset.sum_congr (M := ℝ) rfl fun r _ => ?_
  have hrate : N.massActionRate κ r (x₀ + u • v)
      = κ.k r * (N.reaction r).source.massActionMonomial (x₀ + u • v) := rfl
  rw [hrate]
  field_simp

/-- **The reduced determinant is a sum of signed rates.**  The reduced determinant of a rank-one
network at a class point is the sum, over the reactions, of the signed rate `κ_r c_r` times the
directional derivative of the source monomial along `v`.  Its sign is therefore governed by the
orientations of the reaction vectors along the single stoichiometric direction: this is the
rank-one reading of the *circuit* description of the multistationarity regions. -/
theorem reducedDet_eq_sum_signedRates (N : Network S) (κ : N.RateConstants) {v : Concentration S}
    (hspan : N.stoichSubspace = Submodule.span ℝ {v}) {i₀ : S} (hi₀ : v i₀ ≠ 0)
    (x₀ : Concentration S) (t : ℝ) :
    rankOneReducedDet N κ v i₀ (x₀ + t • v)
      = ∑ r, κ.k r * ((N.reactionVector r) i₀ / v i₀) *
          (∑ j, massActionMonomialGrad (N.reaction r).source (x₀ + t • v) j * v j) := by
  rw [rankOne_reducedDet_eq_deriv N κ hspan hi₀ x₀ t]
  have hfun : (fun u : ℝ => N.lineField κ x₀ v i₀ u)
      = fun u => ∑ r, κ.k r * ((N.reactionVector r) i₀ / v i₀) *
          (N.reaction r).source.massActionMonomial (x₀ + u • v) := by
    funext u
    exact lineField_eq_sum_signedRates N κ hspan hi₀ x₀ u
  have hsum : HasDerivAt (fun u : ℝ => N.lineField κ x₀ v i₀ u)
      (∑ r, κ.k r * ((N.reactionVector r) i₀ / v i₀) *
        (∑ j, massActionMonomialGrad (N.reaction r).source (x₀ + t • v) j * v j)) t := by
    rw [hfun]
    refine HasDerivAt.fun_sum (u := (Finset.univ : Finset N.R)) ?_
    intro r hr
    have h := massActionMonomial_hasDerivAt_along (N.reaction r).source x₀ v t
    exact h.const_mul (κ.k r * ((N.reactionVector r) i₀ / v i₀))
  exact hsum.deriv

/-- **A positive circuit carries no positive steady state.**  If every reaction vector points in the
same direction along `v` — the rank-one version of a *positive circuit* — the scalar field of the
network along the class is strictly positive, and the class carries no positive steady state at
all.  In particular the reduced determinant never vanishes there, and the multistationarity region
is empty. -/
theorem rankOne_noPositiveCircuit_noSteadyState (N : Network S) (κ : N.RateConstants)
    {v : Concentration S} (hspan : N.stoichSubspace = Submodule.span ℝ {v}) {i₀ : S} (hi₀ : v i₀ ≠ 0)
    (x₀ : Concentration S) (hc : ∀ r, 0 < (N.reactionVector r) i₀ / v i₀)
    (hr : Nonempty N.R) :
    ¬ ∃ t : ℝ, (x₀ + t • v).Positive ∧ N.IsMassActionSteadyState κ (x₀ + t • v) := by
  rintro ⟨t, ht, hss⟩
  have hφ : N.lineField κ x₀ v i₀ t = 0 :=
    (N.isMassActionSteadyState_line_iff κ hspan hi₀ x₀ t).mp hss
  rw [lineField_eq_sum_signedRates N κ hspan hi₀ x₀ t] at hφ
  have hpos : 0 < ∑ r, κ.k r * ((N.reactionVector r) i₀ / v i₀) *
      (N.reaction r).source.massActionMonomial (x₀ + t • v) := by
    refine Finset.sum_pos' (s := (Finset.univ : Finset N.R))
      (f := fun r : N.R => κ.k r * ((N.reactionVector r) i₀ / v i₀) *
        (N.reaction r).source.massActionMonomial (x₀ + t • v)) ?_ ⟨hr.some, Finset.mem_univ _, ?_⟩
    · intro r _
      exact le_of_lt (mul_pos (mul_pos (κ.positive r) (hc r))
        (Complex.massActionMonomial_pos ht (N.reaction r).source))
    · exact mul_pos (mul_pos (κ.positive hr.some) (hc hr.some))
        (Complex.massActionMonomial_pos ht (N.reaction hr.some).source)
  linarith

/-! ## The parameter region -/

variable {E₁ E₂ : Type} [Fintype E₁] [Fintype E₂]

/-- **The multistationarity region.**  The parameters `(κ, T)` — rate constants and totals — for
which the class `{x | L x = T}` carries two distinct nondegenerate positive steady states.  This is
the region of leaf M13; the content added here is the *explicit* (reduced-determinant) description
of its rank-one members, `rankOne_multistationary_iff_det_pos`. -/
def MultistationarityRegion (N : Network S) (Z : (S → ℝ) →ₗ[ℝ] (E₁ → ℝ))
    (L : (S → ℝ) →ₗ[ℝ] (E₂ → ℝ)) : Set ((N.R → ℝ) × (E₂ → ℝ)) :=
  NondegRegion N Z L 2

/-- **The multistationarity region in the "rate constants and class representative"
parameterization.**  The set of pairs `(κ', c')` for which the compatibility class of `c'` — the
coset `{x | x - c' ∈ S(N)}`, intersected with the positive orthant — carries two distinct
nondegenerate positive mass-action steady states for the rate constants `κ'`.

This is the region in the shape "rate constants and a representative of the class"; it is *not*
open in its second coordinate, because the class of a representative is a coset of the
stoichiometric subspace and neighbouring representatives sit in different cosets.  The open
multistationarity region is the one in the "rate constants and totals" parameterization,
`MultistationarityRegion` above; for a rank-one network its members are exactly the parameters
for which the reduced determinant is positive at some positive steady state of the class
(`rankOne_multistationary_iff_det_pos`). -/
def ClassMultistationarityRegion (N : Network S) : Set (N.RateConstants × Concentration S) :=
  { q | ∃ x y : Concentration S, x ≠ y ∧ N.StoichCompatible q.2 x ∧ x.Positive ∧
      N.IsMassActionSteadyState q.1 x ∧ N.IsNondegenerateSteadyState q.1 x ∧
      N.StoichCompatible q.2 y ∧ y.Positive ∧ N.IsMassActionSteadyState q.1 y ∧
      N.IsNondegenerateSteadyState q.1 y }

/-- **The multistationarity region is open.**  Each nondegenerate steady state of the class
continues, by the implicit function theorem applied to the augmented system `(Z F_κ(x), L x − T)`,
to nearby parameters; hence the region of parameters carrying two distinct nondegenerate positive
steady states is open. -/
theorem isOpen_multistationarityRegion (N : Network S) (Z : (S → ℝ) →ₗ[ℝ] (E₁ → ℝ))
    (L : (S → ℝ) →ₗ[ℝ] (E₂ → ℝ)) (hZ : ∀ v ∈ N.stoichSubspace, Z v = 0 → v = 0)
    (hL : ∀ v, L v = 0 ↔ v ∈ N.stoichSubspace)
    (hcard : Fintype.card (E₁ ⊕ E₂) = Fintype.card S) :
    IsOpen (MultistationarityRegion N Z L) :=
  isOpen_nondegRegion N Z L hZ hL hcard 2

/-- **The multistationarity region of the rank-one network `X ⇌ Y`, `2X + Y → 3X`, `X + 2Y → 3Y`
is nonempty.**  The Bihan–Dickenstein–Giaroli decorated cells of that network give two distinct
nondegenerate positive steady states in one class, for a suitable choice of totals. -/
theorem multistationarityRegion_nonempty_augmentedCells :
    (MultistationarityRegion Examples.AugmentedCells.net Examples.AugmentedCells.Z
      Examples.AugmentedCells.L).Nonempty := by
  obtain ⟨q, hq⟩ := Examples.AugmentedCells.region_open_nonempty.2
  exact ⟨q, hq⟩

/-! ## A concrete rank-one instance -/

/-- The species `X` of the rank-one instance. -/
def instX : Complex (Fin 2) := ![1, 0]

/-- The species `Y` of the rank-one instance. -/
def instY : Complex (Fin 2) := ![0, 1]

/-- The rank-one network `X ⇌ Y`, `2X + Y → 3X`, `X + 2Y → 3Y`: reaction `0` is `X → Y`,
reaction `1` is `Y → X`, reaction `2` is `2X + Y → 3X` and reaction `3` is `X + 2Y → 3Y`.  All four
reaction vectors are multiples of the single direction `v = X − Y`. -/
def instNet : Network (Fin 2) :=
  ⟨Fin 4, inferInstance, inferInstance, fun r =>
    if r = 0 then ⟨instX, instY⟩ else if r = 1 then ⟨instY, instX⟩
    else if r = 2 then ⟨![2, 1], ![3, 0]⟩ else ⟨![1, 2], ![0, 3]⟩⟩

/-- The single stoichiometric direction of the instance, `v = X − Y`. -/
def instV : Concentration (Fin 2) := ![1, -1]

/-- The reaction type of the instance is `Fin 4`; the numerals below are the reaction indices. -/
instance instNetROfNat0 : OfNat instNet.R 0 := ⟨(0 : Fin 4)⟩
instance instNetROfNat1 : OfNat instNet.R 1 := ⟨(1 : Fin 4)⟩
instance instNetROfNat2 : OfNat instNet.R 2 := ⟨(2 : Fin 4)⟩
instance instNetROfNat3 : OfNat instNet.R 3 := ⟨(3 : Fin 4)⟩

/-- The rate constants `(3, 3, 16, 16)` of the instance: the reversible pair at rate `3`, the two
trimolecular reactions at rate `16`. -/
def instκ : RateConstants instNet :=
  ⟨fun r : Fin 4 => if r = 0 then 3 else if r = 1 then 3 else if r = 2 then 16 else 16, by
    intro r; fin_cases r <;> simp⟩

/-- **The reaction vectors of the instance.**  Reaction `0` (`X → Y`) and reaction `3`
(`X + 2Y → 3Y`) point in the direction `−v`; reactions `1` (`Y → X`) and `2` (`2X + Y → 3X`) point
in the direction `v`. -/
theorem instNet_reactionVector (r : Fin 4) :
    instNet.reactionVector r 0 = (if r = 0 ∨ r = 3 then -1 else 1) ∧
      instNet.reactionVector r 1 = (if r = 0 ∨ r = 3 then 1 else -1) := by
  fin_cases r <;> simp [instNet, instX, instY, Network.reactionVector_apply] <;> norm_num

/-- **The stoichiometric subspace of the instance is the line spanned by `v`.** -/
theorem instNet_stoichSubspace : instNet.stoichSubspace = Submodule.span ℝ {instV} := by
  have h1 : ∀ r : Fin 4, instNet.reactionVector r ∈ Submodule.span ℝ {instV} := by
    intro r
    have h := instNet_reactionVector r
    by_cases h03 : r = 0 ∨ r = 3
    · refine Submodule.mem_span_singleton.mpr ⟨-1, ?_⟩
      funext s
      fin_cases s <;> simp_all [instV, Pi.smul_apply, smul_eq_mul]
    · refine Submodule.mem_span_singleton.mpr ⟨1, ?_⟩
      funext s
      fin_cases s <;> simp_all [instV, Pi.smul_apply, smul_eq_mul]
  show Submodule.span ℝ instNet.reactionVectors = Submodule.span ℝ {instV}
  apply le_antisymm
  · apply Submodule.span_le.2
    rintro _ ⟨r, rfl⟩
    exact h1 r
  · refine Submodule.span_le.2 ?_
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst hx
    have h2 : instNet.reactionVector (1 : Fin 4) = instV := by
      funext s
      fin_cases s <;> simp [instV, instNet_reactionVector]
    rw [← h2]
    show instNet.reactionVector (1 : Fin 4) ∈ instNet.stoichSubspace
    exact instNet.reactionVector_mem_stoichSubspace (1 : Fin 4)

/-- **The scalar field of the instance along the class `{x | x_X + x_Y = 1}`.**  With the class
representative `x₀ = (1/2, 1/2)` the scalar field is `φ(t) = 2t − 32t³`, which vanishes exactly at
`t = 0` and `t = ±1/4`: the class carries three positive steady states. -/
theorem instLineField (t : ℝ) :
    instNet.lineField instκ (fun _ => (1 / 2 : ℝ)) instV 0 t = 2 * t - 32 * t ^ 3 := by
  rw [lineField_eq_sum_signedRates instNet instκ instNet_stoichSubspace (by norm_num [instV]) _ _]
  show (∑ r : Fin 4, instκ.k r * (instNet.reactionVector r 0 / instV 0) *
      (instNet.reaction r).source.massActionMonomial ((fun _ => (1 / 2 : ℝ)) + t • instV))
      = 2 * t - 32 * t ^ 3
  rw [Fin.sum_univ_four]
  simp [instκ, instNet, instX, instY, Complex.massActionMonomial, instV, Pi.add_apply,
    smul_eq_mul, Network.reactionVector_apply]
  ring

/-- **The derivative of the scalar field of the instance.** -/
theorem instLineField_deriv (t : ℝ) :
    deriv (fun s : ℝ => instNet.lineField instκ (fun _ => (1 / 2 : ℝ)) instV 0 s) t
      = 2 - 96 * t ^ 2 := by
  have h1 : HasDerivAt (fun s : ℝ => s ^ 3) (3 * t ^ 2 * 1) t := (hasDerivAt_id t).pow 3
  have h2 : HasDerivAt (fun s : ℝ => 2 * s - 32 * s ^ 3) (2 * 1 - 32 * (3 * t ^ 2 * 1)) t := by
    have h3 := (hasDerivAt_id t).mul_const 2 |>.sub (h1.mul_const 32)
    convert h3 using 1
    · funext s; simp; ring
    · ring
  have hfun : (fun s : ℝ => instNet.lineField instκ (fun _ => (1 / 2 : ℝ)) instV 0 s)
      = fun s => 2 * s - 32 * s ^ 3 := by
    funext s
    exact instLineField s
  rw [hfun]
  convert h2.deriv using 1; ring_nf

/-- **The steady states of the instance in the class `{x | x_X + x_Y = 1}`.**  The three points of
the class with `x_X ∈ {1/4, 1/2, 3/4}` are positive steady states, and their reduced determinants
are `-4`, `2` and `-4`: the middle one has a *positive* reduced determinant, which is the
Conradi–Feliu–Mincheva–Wiuf signature of a multistationary class. -/
theorem inst_steadyState (t : ℝ) (ht : t = -1 / 4 ∨ t = 0 ∨ t = 1 / 4) :
    (instNet.IsMassActionSteadyState instκ ((fun _ => (1 / 2 : ℝ)) + t • instV)) ∧
      ((fun _ => (1 / 2 : ℝ)) + t • instV : Concentration (Fin 2)).Positive ∧
      (instNet.rankOneReducedDet instκ instV 0 ((fun _ => (1 / 2 : ℝ)) + t • instV) = 2 - 96 * t ^ 2) := by
  have hline : instNet.lineField instκ (fun _ => (1 / 2 : ℝ)) instV 0 t = 2 * t - 32 * t ^ 3 :=
    instLineField t
  constructor
  · rw [instNet.isMassActionSteadyState_line_iff instκ instNet_stoichSubspace
      (by norm_num [instV] : instV 0 ≠ 0) _ _]
    rw [hline]
    rcases ht with h | h | h <;> subst h <;> ring
  · constructor
    · intro s
      rcases ht with h | h | h <;> subst h <;> fin_cases s <;>
        simp [instV, Pi.add_apply, smul_eq_mul] <;> norm_num
    · rw [rankOne_reducedDet_eq_deriv instNet instκ instNet_stoichSubspace
        (by norm_num [instV] : instV 0 ≠ 0) _ _]
      rw [instLineField_deriv]

/-- **The instance is multistationary: the class carries three positive steady states, and the
middle one has a positive reduced determinant.**  This is the explicit rank-one instance of the
multistationarity region of leaf M13: the parameters `(κ, T)` of the instance lie in the region,
the region being described by the sign of the reduced determinant. -/
theorem inst_multistationary :
    (instNet.IsMassActionSteadyState instκ ((fun _ => (1 / 2 : ℝ)) + ((-1 / 4 : ℝ)) • instV)) ∧
      (instNet.IsMassActionSteadyState instκ ((fun _ => (1 / 2 : ℝ)) + (0 : ℝ) • instV)) ∧
      (instNet.IsMassActionSteadyState instκ ((fun _ => (1 / 2 : ℝ)) + ((1 / 4 : ℝ)) • instV)) ∧
      0 < instNet.rankOneReducedDet instκ instV 0 ((fun _ => (1 / 2 : ℝ)) + (0 : ℝ) • instV) ∧
      instNet.rankOneReducedDet instκ instV 0
        ((fun _ => (1 / 2 : ℝ)) + ((-1 / 4 : ℝ)) • instV) < 0 ∧
      instNet.rankOneReducedDet instκ instV 0
        ((fun _ => (1 / 2 : ℝ)) + ((1 / 4 : ℝ)) • instV) < 0 := by
  have hm := inst_steadyState (0 : ℝ) (Or.inr (Or.inl rfl))
  have hl := inst_steadyState (-1 / 4 : ℝ) (Or.inl rfl)
  have hr := inst_steadyState (1 / 4 : ℝ) (Or.inr (Or.inr rfl))
  refine ⟨hl.1, hm.1, hr.1, ?_, ?_, ?_⟩
  · rw [hm.2.2]; norm_num
  · rw [hl.2.2]; norm_num
  · rw [hr.2.2]; norm_num

end Network

end CRNT
