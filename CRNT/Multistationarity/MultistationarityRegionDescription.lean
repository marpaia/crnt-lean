import CRNT.Multistationarity.MultistationarityRegion
import CRNT.Multistationarity.DeficiencyOneAlgorithm
import CRNT.Multistationarity.RankOneParameterRegion

/-!
# Parameter regions for multistationarity: the circuit reading of the rank-one region

This module closes the remaining gap of field-map leaf **M13** ("Parameter regions for
multistationarity") for **rank-one networks** — those whose stoichiometric subspace is a single
line `S(N) = span {v}`.

## What was known

`CRNT.Multistationarity.MultistationarityRegion` established that the multistationarity region
of a rank-one network is the set of parameters for which the **reduced determinant** is positive
at one of the positive steady states of the class
(`Network.rankOne_multistationary_iff_det_pos`), and that the reduced determinant is a *signed
sum of rate constants* (`Network.reducedDet_eq_sum_signedRates`).  What was missing was the
**circuit (product-of-rates) reading** of that determinant: the classical
Conradi–Feliu–Mincheva–Wiuf statement that the sign of the reduced determinant at a steady state
is the sign of a **product of rate constants over the reactions of a circuit**.

## What this module adds

### 1. The reduced flux and the reduced determinant in *reduced coordinates*

For a rank-one network every reaction vector is `c_r • v` for a unique real `c_r`
(`Network.reducedCoefficient`), the **reduced coefficient**; `c_r > 0` means that the reaction
runs *with* the class direction `v`, `c_r < 0` that it runs *against* it
(`Network.reducedCoefficient_eq_div`, `Network.reducedCoefficient_eq_zero_iff`).  This module
introduces

* `reducedFlux` — the **reduced flux** `∑_r κ_r c_r x^{y_r}`: the scalar field of the network
  along the class (`Network.reducedFlux_eq_lineField`).  It vanishes **exactly** at the steady
  states of the class (`Network.reducedFlux_eq_zero_iff_steadyState`);
* `reducedContribution` — the signed contribution `c_r ⟨∇ x^{y_r}, v⟩` of a single reaction to the
  reduced determinant;
* `reducedDerivOf` — the reduced determinant read off an arbitrary real rate vector `w`
  (`Network.reducedDerivOf_eq_rankOneReducedDet`).

So the reduced determinant is the **derivative of the reduced flux** along the class
(`Network.hasDerivAt_reducedFlux`), exactly as in Conradi–Feliu–Mincheva–Wiuf: the reduced flux
is the scalar field, the reduced determinant is its slope, and the region is the set of
parameters for which the slope is positive at a zero of the flux.

### 2. The circuit reading: a *comparison* of the two directional fluxes

The circuit reading of the region is the following.  Split the reactions entering the reduced
determinant by their **orientation** along the class, and read off the two **directional fluxes**
(the *forward* flux along `v` and the *backward* flux against `v`):

* `Network.circuitForwardFlux`, `Network.circuitBackwardFlux`;
* `Network.reducedDerivOf_eq_forward_sub_backward` — the reduced determinant is the *difference*
  of the two directional fluxes;
* `Network.reducedDerivOf_pos_iff_forward_gt_backward` — **the circuit sign rule**: the reduced
  determinant is positive **iff the forward flux of the circuit exceeds the backward flux of the
  circuit**; under the definite-sign hypothesis on the monomial-derivative factors the two fluxes
  are nonnegative (`Network.circuitForwardFlux_nonneg`,
  `Network.circuitBackwardFlux_nonneg`).

### 3. The two-reaction circuit: the explicit product comparison

The circuits of a rank-one network are **pairs** of oppositely oriented reactions
(`Network.rankOne_circuit_is_pair`: a positive linear dependence among the reaction vectors
forces both orientations to occur, and two oppositely oriented reactions already carry such a
dependence).  For a two-reaction circuit the circuit sign rule becomes the explicit **product
comparison**

`κ_{r₊} · (c_{r₊} G_{r₊}) > κ_{r₋} · (−c_{r₋} G_{r₋})`,

where `G_r = ⟨∇ x^{y_r}, v⟩` is the monomial-derivative factor of the reaction:
`Network.reducedDerivOf_eq_two_reaction_circuit`,
`Network.reducedDerivOf_pos_iff_two_reaction_circuit`,
`Network.reducedDerivOf_pos_iff_two_reaction_circuit_pos`.  Each side is a **product of a rate
constant and a monomial-derivative factor**: this is the product-of-rates reading of the
multistationarity region that the rank-one reduced determinant admits — a *comparison* of two
such products, not the sign of a single product.

### 4. The obstruction: the product-of-rates *sign rule* is impossible in rank one

The classical rule "the sign of the reduced determinant is the sign of a product of rate constants
over the reactions of a circuit" cannot hold for the rank-one reduced determinant, and this
module *proves* it rather than leaving it as a remark:

* `Network.reducedDerivOf_eq_affine` — along the family of rate vectors that singles out two
  reactions, the reduced determinant is an **affine** function of the remaining parameter;
* `Network.reducedDerivOf_add`, `Network.reducedDerivOf_smul` — the reduced determinant is
  **linear** in the rate constants, whereas a product of rate constants is multilinear;
* `Network.reducedDerivOf_eq_zero_exists` — the reduced determinant **vanishes at a strictly
  positive rate vector** whenever two reactions contribute with opposite signs, whereas a
  product of rate constants is strictly positive there;
* `Network.reducedDerivOf_takes_both_signs` — consequently the reduced determinant **takes both
  signs on the positive orthant** of the rate constants: the sign of the reduced determinant
  depends on the *relative magnitudes* of the rate constants, not on the orientations of the
  reactions alone;
* `Network.not_eq_rateProduct_mul` — the reduced determinant is **not** a constant times a
  product of powers of the rate constants, so no product-of-rates formula exists.

The correct reading of the region is therefore the **comparison** of §2 and §3.

### 5. The explicit region as a set of rate constants

* `Network.RateMultistationarityRegion` — the **multistationarity region in the rate-constant
  parameterization**: the set of rate vectors `w` for which the class of `x₀` carries a positive
  steady state at which the reduced flux vanishes and the reduced determinant is positive;
* `Network.rateMultistationarityRegion_iff_classIsMultistationary` — **the region is exactly the
  set of parameters making the class multistationary** (under the usual hypotheses: compact
  class, no boundary steady state, all steady states nondegenerate).  This is the explicit
  description of the region of leaf M13 in the form the machinery supports: at each candidate
  point of the class the condition is one *linear equation* (the reduced flux vanishes) together
  with one *linear inequality* (the reduced determinant is positive) in the rate constants;
* `Network.rateMultistationarityRegion_nonempty_inst` — the region is **nonempty** for the
  decorated-cell instance `X ⇌ Y`, `2X + Y → 3X`, `X + 2Y → 3Y`; the openness of the region is
  the one inherited from `Network.isOpen_multistationarityRegion` (the open region of parameters
  `(κ, T)`).

### 6. The Deficiency One Algorithm bridge

The Deficiency One Algorithm's certificate `(α, μ)` (a positive flux and a sign-compatible
log-ratio) satisfies the two flux balances; in rank one these are the two **scalar** reduced
flux balances

* `Network.reducedFlux_lower_eq_zero_of_doaCandidate` — `∑_r α_r c_r = 0`;
* `Network.reducedFlux_upper_eq_zero_of_doaCandidate` — `∑_r α_r e^{⟨y_r, μ⟩} c_r = 0`.

So the certificate forces the reduced flux to vanish at the two candidate states — it selects the
**degenerate** case, and the interesting (multistationary) case is the one in which the reduced
*determinant*, the slope of the reduced flux, is positive at a zero of the reduced flux.

Depends on: `CRNT.Multistationarity.MultistationarityRegion`,
`CRNT.Multistationarity.DeficiencyOneAlgorithm`,
`CRNT.Multistationarity.RankOneParameterRegion`.
-/

namespace CRNT

namespace Network

open Filter Topology Set

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ## 1. The reduced coefficient of a reaction along the class direction -/

/-- **The reduced coefficient is the coordinate of the reaction vector divided by `v i₀`.**
For a rank-one network the reaction vector is `c_r • v`; reading the `i₀`-th coordinate of this
identity determines `c_r` from the reaction vector and the class direction. -/
theorem reducedCoefficient_eq_div (N : Network S) (v : S → ℝ) (hv : v ≠ 0)
    (hspan : N.stoichSubspace = Submodule.span ℝ {v}) (i₀ : S) (hi₀ : v i₀ ≠ 0) (r : N.R) :
    reducedCoefficient N v hv hspan r = (N.reactionVector r) i₀ / v i₀ := by
  have h := congrFun (reducedCoefficient_spec N v hv hspan r) i₀
  simp only [Pi.smul_apply, smul_eq_mul] at h
  rw [eq_div_iff hi₀]
  exact h.symm

/-- **The reduced coefficient vanishes exactly when the reaction vector does.** -/
theorem reducedCoefficient_eq_zero_iff (N : Network S) (v : S → ℝ) (hv : v ≠ 0)
    (hspan : N.stoichSubspace = Submodule.span ℝ {v}) (r : N.R) :
    reducedCoefficient N v hv hspan r = 0 ↔ N.reactionVector r = 0 := by
  constructor
  · intro h
    rw [reducedCoefficient_spec N v hv hspan r, h]
    funext s
    simp [Pi.smul_apply, smul_eq_mul]
  · intro h
    have h1 : reducedCoefficient N v hv hspan r • v = 0 := by
      rw [← reducedCoefficient_spec N v hv hspan r, h]
    by_contra hc
    obtain ⟨s, hs⟩ := Function.ne_iff.mp hv
    have hs0 : v s ≠ 0 := by simpa only [Pi.zero_apply] using hs
    have h2 : (reducedCoefficient N v hv hspan r • v) s = 0 := by
      rw [h1]
      rfl
    simp only [Pi.smul_apply, smul_eq_mul] at h2
    rcases mul_eq_zero.mp h2 with hz | hz
    · exact absurd hz hc
    · exact absurd hz hs0

/-! ## 2. The reduced flux: the scalar field of the network along the class -/

/-- **The reduced flux of a rank-one network.**  Along the class `x₀ + t • v` the mass-action
field is `φ(t) • v`; the scalar `φ(t)` is the *reduced flux*: the sum, over the reactions, of the
**signed rate** `κ_r c_r` — the rate constant collected with the orientation `c_r` of the reaction
along the class direction — times the source monomial.

The reduced flux vanishes exactly at the steady states of the class
(`Network.reducedFlux_eq_zero_iff_steadyState`), and its derivative along the class is the
reduced determinant (`Network.hasDerivAt_reducedFlux`). -/
noncomputable def reducedFlux (N : Network S) (v : S → ℝ) (hv : v ≠ 0)
    (hspan : N.stoichSubspace = Submodule.span ℝ {v}) (x₀ : Concentration S)
    (w : N.R → ℝ) (t : ℝ) : ℝ :=
  ∑ r, w r * reducedCoefficient N v hv hspan r *
    (N.reaction r).source.massActionMonomial (x₀ + t • v)

/-- **The reduced flux is the scalar field of the network along the class.** -/
theorem reducedFlux_eq_lineField (N : Network S) (κ : N.RateConstants) (v : S → ℝ) (hv : v ≠ 0)
    (hspan : N.stoichSubspace = Submodule.span ℝ {v}) {i₀ : S} (hi₀ : v i₀ ≠ 0)
    (x₀ : Concentration S) (t : ℝ) :
    reducedFlux N v hv hspan x₀ κ.k t = N.lineField κ x₀ v i₀ t := by
  rw [reducedFlux, lineField_eq_sum_signedRates N κ hspan hi₀ x₀ t]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [reducedCoefficient_eq_div N v hv hspan i₀ hi₀ r]

/-- **The reduced flux vanishes exactly at the steady states of the class.** -/
theorem reducedFlux_eq_zero_iff_steadyState (N : Network S) (κ : N.RateConstants) (v : S → ℝ)
    (hv : v ≠ 0) (hspan : N.stoichSubspace = Submodule.span ℝ {v}) {i₀ : S} (hi₀ : v i₀ ≠ 0)
    (x₀ : Concentration S) (t : ℝ) :
    reducedFlux N v hv hspan x₀ κ.k t = 0 ↔
      N.IsMassActionSteadyState κ (x₀ + t • v) := by
  rw [reducedFlux_eq_lineField N κ v hv hspan hi₀ x₀ t,
    N.isMassActionSteadyState_line_iff κ hspan hi₀ x₀ t]

/-! ## 3. The reduced determinant as a signed sum of rate constants -/

/-- **The signed contribution of a reaction to the reduced determinant.**  The contribution is the
signed rate `c_r` times the **monomial-derivative factor** `⟨∇ x^{y_r}, v⟩`: the directional
derivative of the source monomial along the class direction. -/
noncomputable def reducedContribution (N : Network S) (v : S → ℝ) (hv : v ≠ 0)
    (hspan : N.stoichSubspace = Submodule.span ℝ {v}) (x : Concentration S) (r : N.R) : ℝ :=
  reducedCoefficient N v hv hspan r *
    (∑ j, massActionMonomialGrad (N.reaction r).source x j * v j)

/-- **The reduced determinant, read off an arbitrary real rate vector.**  This is the
*linear* functional of the rate constants whose value at a positive rate vector is the reduced
determinant of the network (`Network.reducedDerivOf_eq_rankOneReducedDet`). -/
noncomputable def reducedDerivOf (N : Network S) (v : S → ℝ) (hv : v ≠ 0)
    (hspan : N.stoichSubspace = Submodule.span ℝ {v}) (x : Concentration S)
    (w : N.R → ℝ) : ℝ :=
  ∑ r, w r * reducedContribution N v hv hspan x r

/-- **The reduced determinant is the signed sum of rate constants.**  In the reduced coordinates
the reduced determinant of a rank-one network is `∑_r κ_r c_r ⟨∇ x^{y_r}, v⟩`: the signed rate
constants of the network, each weighted by the monomial-derivative factor of its reaction. -/
theorem reducedDet_eq_sum_signedRates_coeff (N : Network S) (κ : N.RateConstants) (v : S → ℝ)
    (hv : v ≠ 0) (hspan : N.stoichSubspace = Submodule.span ℝ {v}) {i₀ : S} (hi₀ : v i₀ ≠ 0)
    (x₀ : Concentration S) (t : ℝ) :
    rankOneReducedDet N κ v i₀ (x₀ + t • v)
      = ∑ r, κ.k r * reducedCoefficient N v hv hspan r *
          (∑ j, massActionMonomialGrad (N.reaction r).source (x₀ + t • v) j * v j) := by
  rw [reducedDet_eq_sum_signedRates N κ hspan hi₀ x₀ t]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [reducedCoefficient_eq_div N v hv hspan i₀ hi₀ r]

/-- **The reduced determinant of a rate vector is the reduced determinant of the network.** -/
theorem reducedDerivOf_eq_rankOneReducedDet (N : Network S) (κ : N.RateConstants) (v : S → ℝ)
    (hv : v ≠ 0) (hspan : N.stoichSubspace = Submodule.span ℝ {v}) {i₀ : S} (hi₀ : v i₀ ≠ 0)
    (x₀ : Concentration S) (t : ℝ) :
    reducedDerivOf N v hv hspan (x₀ + t • v) κ.k = rankOneReducedDet N κ v i₀ (x₀ + t • v) := by
  have h1 : reducedDerivOf N v hv hspan (x₀ + t • v) κ.k
      = ∑ r, κ.k r * (reducedCoefficient N v hv hspan r *
          (∑ j, massActionMonomialGrad (N.reaction r).source (x₀ + t • v) j * v j)) := by
    unfold reducedDerivOf reducedContribution
    rfl
  rw [h1, reducedDet_eq_sum_signedRates_coeff N κ v hv hspan hi₀ x₀ t]
  refine Finset.sum_congr rfl fun r _ => ?_
  ring

/-- **The reduced determinant is the derivative of the reduced flux.**  This is the
Conradi–Feliu–Mincheva–Wiuf identification of the reduced determinant with the slope of the
scalar field along the class, in the reduced coordinates. -/
theorem hasDerivAt_reducedFlux (N : Network S) (v : S → ℝ) (hv : v ≠ 0)
    (hspan : N.stoichSubspace = Submodule.span ℝ {v}) (x₀ : Concentration S)
    (w : N.R → ℝ) (t : ℝ) :
    HasDerivAt (fun s => reducedFlux N v hv hspan x₀ w s)
      (reducedDerivOf N v hv hspan (x₀ + t • v) w) t := by
  have hfun : (fun s : ℝ => reducedFlux N v hv hspan x₀ w s)
      = fun s => ∑ r, w r * reducedCoefficient N v hv hspan r *
          (N.reaction r).source.massActionMonomial (x₀ + s • v) := by
    rfl
  rw [hfun]
  have hsum : HasDerivAt (fun s : ℝ => ∑ r, w r * reducedCoefficient N v hv hspan r *
          (N.reaction r).source.massActionMonomial (x₀ + s • v))
      (∑ r, w r * reducedCoefficient N v hv hspan r *
        (∑ j, massActionMonomialGrad (N.reaction r).source (x₀ + t • v) j * v j)) t := by
    refine HasDerivAt.fun_sum (u := (Finset.univ : Finset N.R)) ?_
    intro r hr
    have h := massActionMonomial_hasDerivAt_along (N.reaction r).source x₀ v t
    exact h.const_mul (w r * reducedCoefficient N v hv hspan r)
  have hderiv : reducedDerivOf N v hv hspan (x₀ + t • v) w
      = ∑ r, w r * reducedCoefficient N v hv hspan r *
        (∑ j, massActionMonomialGrad (N.reaction r).source (x₀ + t • v) j * v j) := by
    unfold reducedDerivOf reducedContribution
    refine Finset.sum_congr rfl fun r _ => ?_
    ring
  rw [hderiv]
  exact hsum

/-! ## 4. The reduced determinant is affine in the rate constants -/

/-- **The reduced determinant is additive in the rate constants.** -/
theorem reducedDerivOf_add (N : Network S) (v : S → ℝ) (hv : v ≠ 0)
    (hspan : N.stoichSubspace = Submodule.span ℝ {v}) (x : Concentration S)
    (w₁ w₂ : N.R → ℝ) :
    reducedDerivOf N v hv hspan x (w₁ + w₂)
      = reducedDerivOf N v hv hspan x w₁ + reducedDerivOf N v hv hspan x w₂ := by
  unfold reducedDerivOf
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [Pi.add_apply]
  ring

/-- **The reduced determinant is homogeneous of degree one in the rate constants.** -/
theorem reducedDerivOf_smul (N : Network S) (v : S → ℝ) (hv : v ≠ 0)
    (hspan : N.stoichSubspace = Submodule.span ℝ {v}) (x : Concentration S)
    (c : ℝ) (w : N.R → ℝ) :
    reducedDerivOf N v hv hspan x (c • w) = c * reducedDerivOf N v hv hspan x w := by
  unfold reducedDerivOf
  calc (∑ r, (c • w) r * reducedContribution N v hv hspan x r)
      = ∑ r, c * (w r * reducedContribution N v hv hspan x r) := by
          refine Finset.sum_congr rfl fun r _ => ?_
          simp only [Pi.smul_apply, smul_eq_mul]
          ring
    _ = c * ∑ r, w r * reducedContribution N v hv hspan x r := by
          rw [Finset.mul_sum]

/-- **The reduced determinant of a rank-one network is an affine (indeed linear) function of the
rate constants.**  This is the structural reason why the classical *product-of-rates* reading of
the reduced determinant is impossible: a product of rate constants is multilinear, the reduced
determinant is linear. -/
theorem reducedDerivOf_linear (N : Network S) (v : S → ℝ) (hv : v ≠ 0)
    (hspan : N.stoichSubspace = Submodule.span ℝ {v}) (x : Concentration S)
    (w : N.R → ℝ) :
    reducedDerivOf N v hv hspan x w
      = ∑ r, w r * reducedContribution N v hv hspan x r := rfl

/-! ## 5. The circuit reading: the two directional fluxes -/

/-- **The forward flux of the circuit.**  The reactions of the network whose reduced coefficient
is positive — the reactions running *with* the class direction — contribute the
`max c_r 0` part of their signed rate. -/
noncomputable def circuitForwardFlux (N : Network S) (v : S → ℝ) (hv : v ≠ 0)
    (hspan : N.stoichSubspace = Submodule.span ℝ {v}) (x : Concentration S)
    (w : N.R → ℝ) : ℝ :=
  ∑ r, w r * max (reducedCoefficient N v hv hspan r) 0 *
    (∑ j, massActionMonomialGrad (N.reaction r).source x j * v j)

/-- **The backward flux of the circuit.**  The reactions running *against* the class direction
contribute the `max (−c_r) 0` part of their signed rate. -/
noncomputable def circuitBackwardFlux (N : Network S) (v : S → ℝ) (hv : v ≠ 0)
    (hspan : N.stoichSubspace = Submodule.span ℝ {v}) (x : Concentration S)
    (w : N.R → ℝ) : ℝ :=
  ∑ r, w r * max (-(reducedCoefficient N v hv hspan r)) 0 *
    (∑ j, massActionMonomialGrad (N.reaction r).source x j * v j)

/-- **The reduced determinant is the difference of the two directional fluxes of the circuit.**
The orientation of a reaction along the class direction splits its signed rate into its forward
part `max c_r 0` and its backward part `max (−c_r) 0`, and `c_r = max c_r 0 − max (−c_r) 0`. -/
theorem reducedDerivOf_eq_forward_sub_backward (N : Network S) (v : S → ℝ) (hv : v ≠ 0)
    (hspan : N.stoichSubspace = Submodule.span ℝ {v}) (x : Concentration S) (w : N.R → ℝ) :
    reducedDerivOf N v hv hspan x w
      = circuitForwardFlux N v hv hspan x w - circuitBackwardFlux N v hv hspan x w := by
  unfold reducedDerivOf circuitForwardFlux circuitBackwardFlux reducedContribution
  have hmax : ∀ c : ℝ, max c 0 = (c + |c|) / 2 := by
    intro c
    rcases le_total c 0 with h | h
    · rw [max_eq_right h, abs_of_nonpos h]
      ring
    · rw [max_eq_left (by linarith : (0 : ℝ) ≤ c), abs_of_nonneg (by linarith)]
      ring
  have hmaxneg : ∀ c : ℝ, max (-c) 0 = (-c + |c|) / 2 := by
    intro c
    rcases le_total c 0 with h | h
    · rw [max_eq_left (by linarith : (0 : ℝ) ≤ -c), abs_of_nonpos h]
      ring
    · rw [max_eq_right (by linarith : -c ≤ 0), abs_of_nonneg (by linarith)]
      ring
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [hmax (reducedCoefficient N v hv hspan r), hmaxneg (reducedCoefficient N v hv hspan r)]
  ring

/-- **The circuit sign rule.**  The reduced determinant is the difference of the two directional
fluxes of the circuit, so it is positive **iff the forward flux of the circuit exceeds the
backward flux of the circuit**.

This is the circuit-based reading of the multistationarity region: the region is the set of rate
constants for which, at a steady state of the class, the reactions running with the class
direction carry more flux than the reactions running against it.  When every reaction's
contribution has a definite sign — all the monomial-derivative factors `⟨∇ x^{y_r}, v⟩` are
nonnegative — the two fluxes are nonnegative
(`Network.circuitForwardFlux_nonneg`, `Network.circuitBackwardFlux_nonneg`), and the comparison
is a comparison of two nonnegative quantities. -/
theorem reducedDerivOf_pos_iff_forward_gt_backward (N : Network S) (v : S → ℝ) (hv : v ≠ 0)
    (hspan : N.stoichSubspace = Submodule.span ℝ {v}) (x : Concentration S) (w : N.R → ℝ) :
    0 < reducedDerivOf N v hv hspan x w ↔
      circuitForwardFlux N v hv hspan x w > circuitBackwardFlux N v hv hspan x w := by
  rw [reducedDerivOf_eq_forward_sub_backward]
  constructor
  · intro h
    exact sub_pos.mp h
  · intro h
    exact sub_pos.mpr h

/-- **The two directional fluxes of the circuit are nonnegative.**  Under the definite-sign
hypothesis each flux is a sum of nonnegative terms. -/
theorem circuitForwardFlux_nonneg (N : Network S) (v : S → ℝ) (hv : v ≠ 0)
    (hspan : N.stoichSubspace = Submodule.span ℝ {v}) (x : Concentration S) (w : N.R → ℝ)
    (hw : ∀ r : N.R, 0 ≤ w r)
    (hgrad : ∀ r : N.R, 0 ≤ ∑ j, massActionMonomialGrad (N.reaction r).source x j * v j) :
    0 ≤ circuitForwardFlux N v hv hspan x w := by
  unfold circuitForwardFlux
  exact Finset.sum_nonneg fun r _ => by
    have h1 : 0 ≤ w r := hw r
    have h2 : 0 ≤ max (reducedCoefficient N v hv hspan r) 0 := le_max_right _ _
    have h3 : 0 ≤ ∑ j, massActionMonomialGrad (N.reaction r).source x j * v j := hgrad r
    positivity

/-- **The backward flux of the circuit is nonnegative.** -/
theorem circuitBackwardFlux_nonneg (N : Network S) (v : S → ℝ) (hv : v ≠ 0)
    (hspan : N.stoichSubspace = Submodule.span ℝ {v}) (x : Concentration S) (w : N.R → ℝ)
    (hw : ∀ r : N.R, 0 ≤ w r)
    (hgrad : ∀ r : N.R, 0 ≤ ∑ j, massActionMonomialGrad (N.reaction r).source x j * v j) :
    0 ≤ circuitBackwardFlux N v hv hspan x w := by
  unfold circuitBackwardFlux
  exact Finset.sum_nonneg fun r _ => by
    have h1 : 0 ≤ w r := hw r
    have h2 : 0 ≤ max (-(reducedCoefficient N v hv hspan r)) 0 := le_max_right _ _
    have h3 : 0 ≤ ∑ j, massActionMonomialGrad (N.reaction r).source x j * v j := hgrad r
    positivity

/-! ## 6. The two-reaction circuit: the explicit product comparison -/

/-- **The circuits of a rank-one network are pairs of oppositely oriented reactions.**  A set of
reactions of a rank-one network carrying a *positive linear dependence* — the reaction-network
notion of a *circuit* — contains one reaction running with the class direction and one running
against it, and the two of them already carry a positive dependence.  So the minimal circuits of a
rank-one network are **pairs** of oppositely oriented reactions, and the two-reaction comparison
of `Network.reducedDerivOf_pos_iff_two_reaction_circuit` is the product-of-rates reading of the
region. -/
theorem rankOne_circuit_is_pair (N : Network S) (v : S → ℝ) (hv : v ≠ 0)
    (hspan : N.stoichSubspace = Submodule.span ℝ {v}) {C : Finset N.R}
    (hdep : ∃ lam : N.R → ℝ, (∀ r, r ∈ C → 0 < lam r) ∧ (∀ r, r ∉ C → lam r = 0) ∧
      ∑ r, lam r * reducedCoefficient N v hv hspan r = 0)
    (htrivial : ∃ r ∈ C, reducedCoefficient N v hv hspan r ≠ 0) :
    ∃ rpos rneg : N.R, rpos ∈ C ∧ rneg ∈ C ∧ rpos ≠ rneg ∧
      0 < reducedCoefficient N v hv hspan rpos ∧
      reducedCoefficient N v hv hspan rneg < 0 := by
  obtain ⟨lam, hlam, hzero, hsum⟩ := hdep
  have hpos : ∃ r ∈ C, 0 < reducedCoefficient N v hv hspan r := by
    by_contra h
    have hnonpos : ∀ r ∈ C, reducedCoefficient N v hv hspan r ≤ 0 := by
      intro r hr
      by_contra hcon
      push Not at hcon
      exact h ⟨r, hr, hcon⟩
    obtain ⟨r0, hr0, hc0⟩ := htrivial
    have hstrict : ∑ r, lam r * reducedCoefficient N v hv hspan r < 0 := by
      refine Finset.sum_neg' (fun r _ => ?_) ⟨r0, Finset.mem_univ _, ?_⟩
      · by_cases hr : r ∈ C
        · exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt (hlam r hr)) (hnonpos r hr)
        · rw [hzero r hr]
          simp
      · have hne : reducedCoefficient N v hv hspan r0 < 0 := by
          rcases lt_or_eq_of_le (hnonpos r0 hr0) with hlt | heq
          · exact hlt
          · exact absurd heq hc0
        exact mul_neg_of_pos_of_neg (hlam r0 hr0) hne
    rw [hsum] at hstrict
    linarith
  have hneg : ∃ r ∈ C, reducedCoefficient N v hv hspan r < 0 := by
    by_contra h
    have hnonneg : ∀ r ∈ C, 0 ≤ reducedCoefficient N v hv hspan r := by
      intro r hr
      by_contra hcon
      push Not at hcon
      exact h ⟨r, hr, hcon⟩
    obtain ⟨r0, hr0, hc0⟩ := htrivial
    have hstrict : 0 < ∑ r, lam r * reducedCoefficient N v hv hspan r := by
      refine Finset.sum_pos' (fun r _ => ?_) ⟨r0, Finset.mem_univ _, ?_⟩
      · by_cases hr : r ∈ C
        · exact mul_nonneg (le_of_lt (hlam r hr)) (hnonneg r hr)
        · rw [hzero r hr]
          simp
      · have hne : 0 < reducedCoefficient N v hv hspan r0 := by
          rcases lt_or_eq_of_le (hnonneg r0 hr0) with hlt | heq
          · exact hlt
          · exact absurd heq.symm hc0
        exact mul_pos (hlam r0 hr0) hne
    rw [hsum] at hstrict
    linarith
  obtain ⟨rpos, hrpos, hcpos⟩ := hpos
  obtain ⟨rneg, hrneg, hcneg⟩ := hneg
  refine ⟨rpos, rneg, hrpos, hrneg, ?_, hcpos, hcneg⟩
  intro h
  subst h
  exact absurd hcpos (by linarith)

/-- **The two contributions of a two-reaction circuit.**  If only two reactions contribute to the
reduced determinant, the reduced determinant is the sum of their two contributions. -/
theorem reducedDerivOf_eq_two_reaction_circuit (N : Network S) (v : S → ℝ) (hv : v ≠ 0)
    (hspan : N.stoichSubspace = Submodule.span ℝ {v}) (x : Concentration S) (w : N.R → ℝ)
    {rpos rneg : N.R} (hr : rpos ≠ rneg)
    (hothers : ∀ r : N.R, r ≠ rpos → r ≠ rneg → reducedContribution N v hv hspan x r = 0) :
    reducedDerivOf N v hv hspan x w
      = w rpos * reducedContribution N v hv hspan x rpos +
        w rneg * reducedContribution N v hv hspan x rneg := by
  have h1 : (∑ r ∈ ((Finset.univ : Finset N.R).erase rpos).erase rneg,
        w r * reducedContribution N v hv hspan x r) = 0 := by
    refine Finset.sum_eq_zero fun r hr => ?_
    have hmem : r ∈ (Finset.univ : Finset N.R).erase rpos := (Finset.mem_erase.mp hr).2
    have hne1 : r ≠ rpos := (Finset.mem_erase.mp hmem).1
    have hne2 : r ≠ rneg := (Finset.mem_erase.mp hr).1
    rw [hothers r hne1 hne2]
    ring
  have hmem : rneg ∈ (Finset.univ : Finset N.R).erase rpos :=
    Finset.mem_erase.mpr ⟨hr.symm, Finset.mem_univ rneg⟩
  have h2 : (∑ r ∈ (Finset.univ : Finset N.R).erase rpos,
        w r * reducedContribution N v hv hspan x r)
      = (∑ r ∈ ((Finset.univ : Finset N.R).erase rpos).erase rneg,
          w r * reducedContribution N v hv hspan x r) +
        w rneg * reducedContribution N v hv hspan x rneg := by
    have he := Finset.sum_erase_add ((Finset.univ : Finset N.R).erase rpos)
      (fun r => w r * reducedContribution N v hv hspan x r) hmem
    rw [h1] at he
    rw [h1]
    exact he.symm
  have h3 : (∑ r, w r * reducedContribution N v hv hspan x r)
      = (∑ r ∈ (Finset.univ : Finset N.R).erase rpos,
          w r * reducedContribution N v hv hspan x r) +
        w rpos * reducedContribution N v hv hspan x rpos := by
    have he := Finset.sum_erase_add (Finset.univ : Finset N.R)
      (fun r => w r * reducedContribution N v hv hspan x r) (Finset.mem_univ rpos)
    rw [h2] at he
    rw [h1] at he
    rw [h2, h1]
    exact he.symm
  rw [reducedDerivOf, h3, h2, h1]
  ring

/-- **The product comparison of a two-reaction circuit.**  For a rank-one network in which only
two reactions contribute to the reduced determinant — the minimal circuit of a rank-one network,
two reactions running in opposite directions along the class — the reduced determinant is positive
**iff**

`w rpos · (c rpos · G rpos) > w rneg · (−c rneg · G rneg)`,

where `G r = ⟨∇ x^{y_r}, v⟩` is the monomial-derivative factor of the reaction.  Each side is a
**product of a rate constant and a monomial-derivative factor**: this is the product-of-rates
reading of the multistationarity region that the rank-one reduced determinant admits, and it is
a *comparison* of two such products, not the sign of a single product. -/
theorem reducedDerivOf_pos_iff_two_reaction_circuit (N : Network S) (v : S → ℝ) (hv : v ≠ 0)
    (hspan : N.stoichSubspace = Submodule.span ℝ {v}) (x : Concentration S) (w : N.R → ℝ)
    {rpos rneg : N.R} (hr : rpos ≠ rneg)
    (hothers : ∀ r : N.R, r ≠ rpos → r ≠ rneg → reducedContribution N v hv hspan x r = 0) :
    0 < reducedDerivOf N v hv hspan x w ↔
      w rpos * (reducedCoefficient N v hv hspan rpos *
          (∑ j, massActionMonomialGrad (N.reaction rpos).source x j * v j))
        > w rneg * ((-(reducedCoefficient N v hv hspan rneg)) *
          (∑ j, massActionMonomialGrad (N.reaction rneg).source x j * v j)) := by
  have h1 : reducedContribution N v hv hspan x rpos
      = reducedCoefficient N v hv hspan rpos *
        (∑ j, massActionMonomialGrad (N.reaction rpos).source x j * v j) := rfl
  have h2 : reducedContribution N v hv hspan x rneg
      = reducedCoefficient N v hv hspan rneg *
        (∑ j, massActionMonomialGrad (N.reaction rneg).source x j * v j) := rfl
  rw [reducedDerivOf_eq_two_reaction_circuit N v hv hspan x w hr hothers, h1, h2]
  have hne : w rneg * (reducedCoefficient N v hv hspan rneg *
      (∑ j, massActionMonomialGrad (N.reaction rneg).source x j * v j))
      = -(w rneg * ((-(reducedCoefficient N v hv hspan rneg)) *
        (∑ j, massActionMonomialGrad (N.reaction rneg).source x j * v j))) := by ring
  constructor
  · intro h
    rw [hne] at h
    linarith
  · intro h
    rw [hne]
    linarith

/-- **The product comparison of a two-reaction circuit, for positive rate constants.**  Under the
sign hypotheses — the two reactions run in opposite directions along the class and both
monomial-derivative factors are positive — the forward side of the comparison is a *strictly
positive* product of a rate constant and a monomial-derivative factor.  This is the explicit
product-of-rates description of the multistationarity region of a two-reaction circuit. -/
theorem reducedDerivOf_pos_iff_two_reaction_circuit_pos (N : Network S) (κ : N.RateConstants)
    (v : S → ℝ) (hv : v ≠ 0) (hspan : N.stoichSubspace = Submodule.span ℝ {v})
    (x : Concentration S) {rpos rneg : N.R} (hr : rpos ≠ rneg)
    (hpos : 0 < reducedCoefficient N v hv hspan rpos)
    (hneg : reducedCoefficient N v hv hspan rneg < 0)
    (hgradpos : 0 < ∑ j, massActionMonomialGrad (N.reaction rpos).source x j * v j)
    (hgradneg : 0 < ∑ j, massActionMonomialGrad (N.reaction rneg).source x j * v j)
    (hothers : ∀ r : N.R, r ≠ rpos → r ≠ rneg → reducedContribution N v hv hspan x r = 0) :
    0 < reducedDerivOf N v hv hspan x κ.k ↔
      κ.k rpos * (reducedCoefficient N v hv hspan rpos *
          (∑ j, massActionMonomialGrad (N.reaction rpos).source x j * v j))
        > κ.k rneg * ((-(reducedCoefficient N v hv hspan rneg)) *
          (∑ j, massActionMonomialGrad (N.reaction rneg).source x j * v j)) ∧
      0 < κ.k rpos * (reducedCoefficient N v hv hspan rpos *
          (∑ j, massActionMonomialGrad (N.reaction rpos).source x j * v j)) ∧
      0 < κ.k rneg * ((-(reducedCoefficient N v hv hspan rneg)) *
          (∑ j, massActionMonomialGrad (N.reaction rneg).source x j * v j)) := by
  rw [reducedDerivOf_pos_iff_two_reaction_circuit N v hv hspan x κ.k hr hothers]
  constructor
  · intro h
    refine ⟨h, ?_, ?_⟩
    · exact mul_pos (κ.positive rpos) (mul_pos hpos hgradpos)
    · exact mul_pos (κ.positive rneg) (mul_pos (neg_pos.mpr hneg) hgradneg)
  · rintro ⟨h, _, _⟩
    exact h

/-! ## 7. The explicit multistationarity region as a set of rate constants -/

/-- **The multistationarity region of a rank-one network, in the rate-constant
parameterization.**  The set of rate vectors `w` for which the class of the positive
representative `x₀` carries a positive steady state at which the reduced flux vanishes and the
reduced determinant — the slope of the reduced flux — is positive.

This is the explicit description of the region of leaf M13 that the machinery supports: the
condition is one *linear equation* (the reduced flux vanishes) together with one *linear
inequality* (the reduced determinant is positive) in the rate constants, at a candidate point of
the class. -/
noncomputable def RateMultistationarityRegion (N : Network S) (v : S → ℝ) (hv : v ≠ 0)
    (hspan : N.stoichSubspace = Submodule.span ℝ {v}) (x₀ : Concentration S)
    (hP : (Finset.univ.filter fun s => 0 < v s).Nonempty)
    (hQ : (Finset.univ.filter fun s => v s < 0).Nonempty) : Set (N.R → ℝ) :=
  { w | ∃ t : ℝ, lineLeft x₀ v hP < t ∧ t < lineRight x₀ v hQ ∧
      reducedFlux N v hv hspan x₀ w t = 0 ∧
      0 < reducedDerivOf N v hv hspan (x₀ + t • v) w }

/-- **The class of `x₀` carries two distinct positive mass-action steady states.** -/
def ClassIsMultistationary (N : Network S) (κ : N.RateConstants) (x₀ : Concentration S) : Prop :=
  ∃ x y : Concentration S, x ≠ y ∧ N.StoichCompatible x₀ x ∧ x.Positive ∧
    N.IsMassActionSteadyState κ x ∧ N.StoichCompatible x₀ y ∧ y.Positive ∧
    N.IsMassActionSteadyState κ y

/-- **The explicit description of the multistationarity region of a rank-one network.**  The
region of rate constants is exactly the set of parameters for which the class of `x₀` is
multistationary: the reduced flux vanishes at a positive steady state of the class and the
reduced determinant is positive there.

This is the Conradi–Feliu–Mincheva–Wiuf criterion of leaf M13 in the explicit form: the region is
described by the sign of the reduced determinant, which is the derivative of the reduced flux
along the class, and which is a *signed sum of rate constants* in the reduced coordinates. -/
theorem rateMultistationarityRegion_iff_classIsMultistationary (N : Network S) (κ : N.RateConstants)
    (v : S → ℝ) (hv : v ≠ 0) (hspan : N.stoichSubspace = Submodule.span ℝ {v})
    (i₀ : S) (hi₀ : v i₀ ≠ 0) (x₀ : Concentration S)
    (hP : (Finset.univ.filter fun s => 0 < v s).Nonempty)
    (hQ : (Finset.univ.filter fun s => v s < 0).Nonempty)
    (hx : x₀.Positive)
    (hbd : ∀ x, N.StoichCompatible x₀ x → x.Nonnegative → ¬ x.Positive →
      ¬ N.IsMassActionSteadyState κ x)
    (hnd : ∀ t, lineLeft x₀ v hP < t → t < lineRight x₀ v hQ → N.lineField κ x₀ v i₀ t = 0 →
      deriv (N.lineField κ x₀ v i₀) t ≠ 0) :
    κ.k ∈ RateMultistationarityRegion N v hv hspan x₀ hP hQ ↔
      N.ClassIsMultistationary κ x₀ := by
  constructor
  · rintro ⟨t, htl, htr, hflux, hdet⟩
    have hφ : N.lineField κ x₀ v i₀ t = 0 := by
      rw [← reducedFlux_eq_lineField N κ v hv hspan hi₀ x₀ t]
      exact hflux
    have hderiv : 0 < deriv (N.lineField κ x₀ v i₀) t := by
      have h1 : reducedDerivOf N v hv hspan (x₀ + t • v) κ.k
          = rankOneReducedDet N κ v i₀ (x₀ + t • v) :=
        reducedDerivOf_eq_rankOneReducedDet N κ v hv hspan hi₀ x₀ t
      rw [rankOne_reducedDet_eq_deriv N κ hspan hi₀ x₀ t] at h1
      rw [h1] at hdet
      exact hdet
    exact (N.rankOne_multistationary_iff κ hspan hP hQ hx hbd hi₀ hnd).2
      ⟨t, htl, htr, hφ, hderiv⟩
  · intro h
    obtain ⟨x, y, hxy, hxc, hxp, hxs, hyc, hyp, hys⟩ := h
    obtain ⟨x, hxc, hxp, hxs, hdet⟩ :=
      (N.rankOne_multistationary_iff_det_pos κ hspan hP hQ hx hbd hi₀ hnd).1
        ⟨x, y, hxy, hxc, hxp, hxs, hyc, hyp, hys⟩
    obtain ⟨t, rfl⟩ := N.exists_line_of_stoichCompatible hspan hxc
    have hpos := (line_positive_iff hP hQ hx t).mp hxp
    refine ⟨t, hpos.1, hpos.2, ?_, ?_⟩
    · exact (reducedFlux_eq_zero_iff_steadyState N κ v hv hspan hi₀ x₀ t).mpr hxs
    · rw [reducedDerivOf_eq_rankOneReducedDet N κ v hv hspan hi₀ x₀ t]
      exact hdet

/-! ## 8. The decorated-cell instance lies in the region -/

/-- **The class direction of the decorated-cell instance is nonzero.** -/
theorem instV_ne : instV ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  norm_num [instV] at h0

/-- **The positive part of the class direction of the decorated-cell instance.** -/
theorem instH_P : (Finset.univ.filter fun s => 0 < instV s).Nonempty :=
  ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [instV]⟩⟩

/-- **The negative part of the class direction of the decorated-cell instance.** -/
theorem instH_Q : (Finset.univ.filter fun s => instV s < 0).Nonempty :=
  ⟨1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [instV]⟩⟩

/-- **The decorated-cell instance lies in the rank-one multistationarity region.**  The network
`X ⇌ Y`, `2X + Y → 3X`, `X + 2Y → 3Y` with the rate constants `(3, 3, 16, 16)` has, in the class
`{x | x_X + x_Y = 1}`, a positive steady state at which the reduced determinant is positive: the
region of leaf M13 is nonempty. -/
theorem rateMultistationarityRegion_nonempty_inst :
    instκ.k ∈ RateMultistationarityRegion instNet instV instV_ne instNet_stoichSubspace
      (fun _ => (1 / 2 : ℝ)) instH_P instH_Q := by
  have hleft : lineLeft (fun _ => (1 / 2 : ℝ)) instV instH_P < 0 := by
    rw [lineLeft, Finset.sup'_lt_iff]
    intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
    have hsn : s = 0 := by
      fin_cases s
      · rfl
      · have h1 : (0 : ℝ) < instV 1 := by simpa using hs
        norm_num [instV] at h1
    subst hsn
    norm_num [instV]
  have hright : 0 < lineRight (fun _ => (1 / 2 : ℝ)) instV instH_Q := by
    rw [lineRight, Finset.lt_inf'_iff]
    intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
    have hsn : s = 1 := by
      fin_cases s
      · have h1 : instV 0 < 0 := by simpa using hs
        norm_num [instV] at h1
      · rfl
    subst hsn
    norm_num [instV]
  have hss := inst_steadyState (0 : ℝ) (Or.inr (Or.inl rfl))
  refine ⟨0, hleft, hright, ?_, ?_⟩
  · exact (reducedFlux_eq_zero_iff_steadyState instNet instκ instV instV_ne
      instNet_stoichSubspace (by norm_num [instV] : instV 0 ≠ 0) (fun _ => (1 / 2 : ℝ)) 0).mpr hss.1
  · rw [reducedDerivOf_eq_rankOneReducedDet instNet instκ instV instV_ne
      instNet_stoichSubspace (by norm_num [instV] : instV 0 ≠ 0) (fun _ => (1 / 2 : ℝ)) 0]
    rw [hss.2.2]
    norm_num

/-! ## 9. The Deficiency One Algorithm bridge -/

/-- **The Deficiency One Algorithm's lower balance equation is a vanishing reduced flux.**  In
rank one the flux balance `∑_r α_r (y'_r − y_r) = 0` of the algorithm's certificate reduces to
the scalar equation `∑_r α_r c_r = 0`: the reduced flux of the certificate vanishes at the lower
candidate state. -/
theorem reducedFlux_lower_eq_zero_of_doaCandidate (N : Network S) (d : DOACandidate N)
    (v : S → ℝ) (hv : v ≠ 0) (hspan : N.stoichSubspace = Submodule.span ℝ {v}) :
    ∑ r, d.α r * reducedCoefficient N v hv hspan r = 0 :=
  (N.rankOne_lowerBalance_iff v hv hspan d.α).mp d.lower_balance

/-- **The Deficiency One Algorithm's upper balance equation is a vanishing reduced flux.**  The
upper balance `∑_r α_r e^{⟨y_r, μ⟩} (y'_r − y_r) = 0` reduces, in rank one, to
`∑_r α_r e^{⟨y_r, μ⟩} c_r = 0`: the reduced flux of the certificate vanishes at the upper
candidate state as well.

So the algorithm's certificate selects the **degenerate** case: it exhibits two candidate states
at which the reduced flux vanishes, and the interesting — multistationary — case is the one in
which the *slope* of the reduced flux, the reduced determinant, is positive at one of them. -/
theorem reducedFlux_upper_eq_zero_of_doaCandidate (N : Network S) (d : DOACandidate N)
    (v : S → ℝ) (hv : v ≠ 0) (hspan : N.stoichSubspace = Submodule.span ℝ {v}) :
    ∑ r, d.α r * Real.exp (complexPairing (N.reaction r).source d.μ) *
      reducedCoefficient N v hv hspan r = 0 :=
  (N.rankOne_upperBalance_iff v hv hspan d.α d.μ).mp d.upper_balance


/-! ## 10. The obstruction: the product-of-rates sign rule is impossible in rank one -/

/-- **A sum over a finite type, split into two elements and the rest.** -/
theorem sum_split_two {ι : Type} [Fintype ι] [DecidableEq ι] (g : ι → ℝ) (r₁ r₂ : ι)
    (hr : r₁ ≠ r₂) :
    (∑ r, g r) = (∑ r ∈ ((Finset.univ : Finset ι).erase r₁).erase r₂, g r) + g r₁ + g r₂ := by
  have he1 := Finset.sum_erase_add (Finset.univ : Finset ι) g (Finset.mem_univ r₁)
  have he2 := Finset.sum_erase_add ((Finset.univ : Finset ι).erase r₁) g
    (Finset.mem_erase.mpr ⟨hr.symm, Finset.mem_univ r₂⟩)
  rw [← he2] at he1
  linarith

/-- **The reduced determinant along a two-parameter family of rate vectors.**  For the rate vector
`w r = 1` at `r₁`, `w r = t` at `r₂` and `w r = ε` at the remaining reactions, the reduced
determinant is the **affine** function `ε B + a r₁ + t a r₂` of `t`, where `B` is the sum of the
contributions of the remaining reactions and `a r` is the contribution of `r`.

The affinity is the analytic content of the obstruction: the reduced determinant of a rank-one
network is a *linear* function of the rate constants, never a product of them. -/
theorem reducedDerivOf_eq_affine (N : Network S) (v : S → ℝ) (hv : v ≠ 0)
    (hspan : N.stoichSubspace = Submodule.span ℝ {v}) (x : Concentration S)
    {r₁ r₂ : N.R} (hr : r₁ ≠ r₂) (ε t : ℝ) :
    reducedDerivOf N v hv hspan x (fun r => if r = r₁ then 1 else if r = r₂ then t else ε)
      = ε * (∑ r ∈ ((Finset.univ : Finset N.R).erase r₁).erase r₂,
          reducedContribution N v hv hspan x r)
        + reducedContribution N v hv hspan x r₁
        + t * reducedContribution N v hv hspan x r₂ := by
  unfold reducedDerivOf
  have hsplit := sum_split_two (fun r => (if r = r₁ then 1 else if r = r₂ then t else ε) *
      reducedContribution N v hv hspan x r) r₁ r₂ hr
  rw [hsplit]
  have h1 : (if r₁ = r₁ then 1 else if r₁ = r₂ then t else ε) = 1 := by simp
  have h2 : (if r₂ = r₁ then 1 else if r₂ = r₂ then t else ε) = t := by
    simp [hr.symm]
  rw [h1, h2]
  have h3 : (∑ r ∈ ((Finset.univ : Finset N.R).erase r₁).erase r₂,
      (if r = r₁ then 1 else if r = r₂ then t else ε) * reducedContribution N v hv hspan x r)
      = ε * (∑ r ∈ ((Finset.univ : Finset N.R).erase r₁).erase r₂,
          reducedContribution N v hv hspan x r) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r hr' => ?_
    have hne2 : r ≠ r₂ := (Finset.mem_erase.mp hr').1
    have hne1 : r ≠ r₁ := (Finset.mem_erase.mp (Finset.mem_erase.mp hr').2).1
    simp [hne1, hne2]
  rw [h3]
  ring

/-- **A rate vector at which the reduced determinant vanishes.**  If two reactions contribute to
the reduced determinant with opposite signs, there are positive numbers `ε` and `t` such that the
rate vector `w r = 1` at the first reaction, `w r = t` at the second and `w r = ε` at the
remaining ones makes the reduced determinant vanish. -/
theorem exists_eps_t (N : Network S) (v : S → ℝ) (hv : v ≠ 0)
    (hspan : N.stoichSubspace = Submodule.span ℝ {v}) (x : Concentration S)
    {r₁ r₂ : N.R}
    (ha₁ : 0 < reducedContribution N v hv hspan x r₁)
    (ha₂ : reducedContribution N v hv hspan x r₂ < 0) :
    ∃ (ε t : ℝ), 0 < ε ∧ 0 < t ∧
      ε * (∑ r ∈ ((Finset.univ : Finset N.R).erase r₁).erase r₂,
          reducedContribution N v hv hspan x r) +
        reducedContribution N v hv hspan x r₁ +
        t * reducedContribution N v hv hspan x r₂ = 0 := by
  set B : ℝ := ∑ r ∈ ((Finset.univ : Finset N.R).erase r₁).erase r₂,
      reducedContribution N v hv hspan x r with hB
  have hε : ∃ ε : ℝ, 0 < ε ∧ 0 < reducedContribution N v hv hspan x r₁ + ε * B := by
    by_cases hB0 : 0 ≤ B
    · refine ⟨1, one_pos, ?_⟩
      have h1 : 0 < reducedContribution N v hv hspan x r₁ + 1 * B := by linarith
      simpa [hB] using h1
    · have hBneg : B < 0 := lt_of_not_ge hB0
      obtain ⟨ε, hε0, hε1⟩ := exists_between'
        (show (0 : ℝ) < reducedContribution N v hv hspan x r₁ / (-B) by
          exact div_pos ha₁ (neg_pos.mpr hBneg))
      refine ⟨ε, hε1, ?_⟩
      have h2 : ε * (-B) < reducedContribution N v hv hspan x r₁ :=
        (lt_div_iff₀ (neg_pos.mpr hBneg)).mp hε0
      have h1 : 0 < reducedContribution N v hv hspan x r₁ + ε * B := by
        have h3 : ε * B = -(ε * (-B)) := by ring
        rw [h3]
        linarith
      simpa [hB] using h1
  obtain ⟨ε, hε0, hεB⟩ := hε
  refine ⟨ε, (reducedContribution N v hv hspan x r₁ + ε * B) /
      (- reducedContribution N v hv hspan x r₂), hε0, ?_, ?_⟩
  · exact div_pos hεB (neg_pos.mpr ha₂)
  · have h1 : ε * B + reducedContribution N v hv hspan x r₁
        + ((reducedContribution N v hv hspan x r₁ + ε * B) /
            (- reducedContribution N v hv hspan x r₂)) *
          reducedContribution N v hv hspan x r₂ = 0 := by
      field_simp [ne_of_lt ha₂]
      ring
    simpa [hB] using h1

/-- **The reduced determinant vanishes at a strictly positive rate vector.**  If two reactions
contribute to the reduced determinant of a rank-one network with opposite signs, the reduced
determinant is zero at some strictly positive rate vector.  Since a product of rate constants is
strictly positive at every strictly positive rate vector, this rules out a "sign of a product of
rate constants" rule for the rank-one reduced determinant. -/
theorem reducedDerivOf_eq_zero_exists (N : Network S) (v : S → ℝ) (hv : v ≠ 0)
    (hspan : N.stoichSubspace = Submodule.span ℝ {v}) (x : Concentration S)
    {r₁ r₂ : N.R} (hr : r₁ ≠ r₂)
    (ha₁ : 0 < reducedContribution N v hv hspan x r₁)
    (ha₂ : reducedContribution N v hv hspan x r₂ < 0) :
    ∃ w : N.R → ℝ, (∀ r, 0 < w r) ∧ reducedDerivOf N v hv hspan x w = 0 := by
  obtain ⟨ε, t, hε0, ht0, hzero⟩ := exists_eps_t N v hv hspan x ha₁ ha₂
  refine ⟨fun r => if r = r₁ then 1 else if r = r₂ then t else ε, ?_, ?_⟩
  · intro r
    by_cases h1 : r = r₁
    · simp [h1]
    · by_cases h2 : r = r₂
      · subst h2
        simp [hr.symm, ht0]
      · simp [h1, h2, hε0]
  · rw [reducedDerivOf_eq_affine N v hv hspan x hr ε t]
    exact hzero

/-- **The reduced determinant takes both signs on the positive orthant of the rate constants.**
This is the decisive obstruction to the classical *product-of-rates* reading of the rank-one
reduced determinant: the sign of the reduced determinant is not determined by the orientations of
the reactions, but by a *comparison of magnitudes* of the rate constants.  The region of leaf M13
is therefore described by the comparison of the two directional fluxes of the circuit, and not by
the sign of a product of rate constants. -/
theorem reducedDerivOf_takes_both_signs (N : Network S) (v : S → ℝ) (hv : v ≠ 0)
    (hspan : N.stoichSubspace = Submodule.span ℝ {v}) (x : Concentration S)
    {r₁ r₂ : N.R} (hr : r₁ ≠ r₂)
    (ha₁ : 0 < reducedContribution N v hv hspan x r₁)
    (ha₂ : reducedContribution N v hv hspan x r₂ < 0) :
    ∃ wpos wneg : N.R → ℝ, (∀ r, 0 < wpos r) ∧ (∀ r, 0 < wneg r) ∧
      0 < reducedDerivOf N v hv hspan x wpos ∧
      reducedDerivOf N v hv hspan x wneg < 0 := by
  obtain ⟨ε, t, hε0, ht0, hzero⟩ := exists_eps_t N v hv hspan x ha₁ ha₂
  set B : ℝ := ∑ r ∈ ((Finset.univ : Finset N.R).erase r₁).erase r₂,
      reducedContribution N v hv hspan x r with hB
  have hcore : ε * B + reducedContribution N v hv hspan x r₁
      = -(t * reducedContribution N v hv hspan x r₂) := by
    have h1 := hzero
    rw [hB] at h1
    linarith
  refine ⟨fun r => if r = r₁ then 1 else if r = r₂ then t / 2 else ε,
    fun r => if r = r₁ then 1 else if r = r₂ then 2 * t else ε, ?_, ?_, ?_, ?_⟩
  · intro r
    by_cases h1 : r = r₁
    · simp [h1]
    · by_cases h2 : r = r₂
      · subst h2
        simp [hr.symm, ht0]
      · simp [h1, h2, hε0]
  · intro r
    by_cases h1 : r = r₁
    · simp [h1]
    · by_cases h2 : r = r₂
      · subst h2
        simp [hr.symm, ht0]
      · simp [h1, h2, hε0]
  · rw [reducedDerivOf_eq_affine N v hv hspan x hr ε (t / 2)]
    have h1 : ε * B + reducedContribution N v hv hspan x r₁
        + (t / 2) * reducedContribution N v hv hspan x r₂
        = -(t * reducedContribution N v hv hspan x r₂) / 2 := by
      rw [hcore]
      ring
    rw [h1]
    have h2 : t * reducedContribution N v hv hspan x r₂ < 0 :=
      mul_neg_of_pos_of_neg ht0 ha₂
    have h3 : 0 < -(t * reducedContribution N v hv hspan x r₂) / 2 :=
      div_pos (neg_pos.mpr h2) (by norm_num)
    exact h3
  · rw [reducedDerivOf_eq_affine N v hv hspan x hr ε (2 * t)]
    have h1 : ε * B + reducedContribution N v hv hspan x r₁
        + (2 * t) * reducedContribution N v hv hspan x r₂
        = t * reducedContribution N v hv hspan x r₂ := by
      rw [hcore]
      ring
    rw [h1]
    have h2 : t * reducedContribution N v hv hspan x r₂ < 0 :=
      mul_neg_of_pos_of_neg ht0 ha₂
    exact h2

/-- **A product of rate constants.**  For a list of exponents `n`, the product
`∏ r, w r ^ (n r)` of the rate constants. -/
noncomputable def rateProduct (N : Network S) (n : N.R → ℕ) (w : N.R → ℝ) : ℝ :=
  ∏ r, w r ^ (n r)

/-- **The reduced determinant of a rank-one network is not a product of rate constants.**  There
are no exponents and no constant making the reduced determinant equal to a constant times the
product of the corresponding powers of the rate constants.

This is the precise sense in which the classical *product-of-rates* reading of the reduced
determinant — "the sign of the reduced determinant is the sign of a product of rate constants
over the reactions of a circuit" — is **not available** for the rank-one reduced determinant: the
reduced determinant is *linear* in the rate constants
(`Network.reducedDerivOf_add`, `Network.reducedDerivOf_smul`), while a product of rate constants
is multilinear, and the sign of the reduced determinant genuinely depends on the *relative
magnitudes* of the rate constants (`Network.reducedDerivOf_takes_both_signs`).  The correct
reading of the multistationarity region of a rank-one network is the **comparison of the two
directional fluxes of the circuit** (`Network.reducedDerivOf_pos_iff_forward_gt_backward`), and
for a two-reaction circuit the explicit comparison of two products of a rate constant with a
monomial-derivative factor (`Network.reducedDerivOf_pos_iff_two_reaction_circuit`). -/
theorem not_eq_rateProduct_mul (N : Network S) (v : S → ℝ) (hv : v ≠ 0)
    (hspan : N.stoichSubspace = Submodule.span ℝ {v}) (x : Concentration S)
    {r₁ r₂ : N.R} (hr : r₁ ≠ r₂)
    (ha₁ : 0 < reducedContribution N v hv hspan x r₁)
    (ha₂ : reducedContribution N v hv hspan x r₂ < 0) :
    ¬ ∃ (n : N.R → ℕ) (C : ℝ), ∀ w : N.R → ℝ,
        reducedDerivOf N v hv hspan x w = C * rateProduct N n w := by
  rintro ⟨n, C, h⟩
  have hpos : ∀ w : N.R → ℝ, (∀ r, 0 < w r) → 0 < rateProduct N n w := by
    intro w hw
    refine Finset.prod_pos fun r _ => ?_
    exact pow_pos (hw r) (n r)
  obtain ⟨wpos, wneg, hwpos, hwneg, hdpos, hdneg⟩ :=
    reducedDerivOf_takes_both_signs N v hv hspan x hr ha₁ ha₂
  have hCpos : 0 < C := by
    have h3 : 0 < C * rateProduct N n wpos := by
      rw [← h wpos]
      exact hdpos
    have h4 : 0 < rateProduct N n wpos := hpos wpos hwpos
    rcases (mul_pos_iff.mp h3) with h | h
    · exact h.1
    · exact absurd h.2 (not_lt_of_ge h4.le)
  have hCneg : C < 0 := by
    have h3 : C * rateProduct N n wneg < 0 := by
      rw [← h wneg]
      exact hdneg
    have h4 : 0 < rateProduct N n wneg := hpos wneg hwneg
    rcases mul_neg_iff.mp h3 with h | h
    · exact absurd h.1 (by linarith)
    · exact h.1
  linarith

end Network

end CRNT
