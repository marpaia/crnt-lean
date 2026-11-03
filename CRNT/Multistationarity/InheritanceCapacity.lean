import CRNT.Multistationarity.InheritanceDependent
import CRNT.Multistationarity.OneReactionReversibleNondegenerate
import CRNT.Multistationarity.TwoReactionAtoms

/-!
# The capacity form of the inheritance of multistationarity

## The theory

Joshi and Shiu (*Atoms of multistationarity in chemical reaction networks*, J. Math. Chem. 51
(2013)) develop the *inheritance* of multistationarity and use it to make the notion of an
**atom of multistationarity** meaningful:

* a network is **multistationary** when some choice of positive rate constants admits two
  distinct positive steady states in one stoichiometric compatibility class — in the repository
  the property `CRNT.Network.HasMultistationarityCapacity`, the *capacity* for multiple steady
  states;
* an **atom** of multistationarity is a multistationary network that is *minimal*: no proper
  subnetwork of it is multistationary.  Minimality is only a meaningful notion because of the
  inheritance theorem: a multistationary network stays multistationary when reactions are added
  at small rates, so a proper *enlargement* of a multistationary network is multistationary and
  can never be an atom; conversely the inheritance in the other direction (a subnetwork of a
  multistationary network need not be multistationary) is what makes the atom notion a genuine
  minimality notion.

## What the repository already contains

* `CRNT.Network.multistationarity_inherited_union` and
  `CRNT.Network.multistationarity_inherited_fullyOpen_union`: two distinct *nondegenerate*
  positive steady states of a full-rank (in particular fully open) network persist, for all
  sufficiently small rates of the added reactions, as two distinct positive steady states of the
  enlarged network in one class (Joshi–Shiu 2013, Theorem 3.1, via the implicit function
  theorem).
* `CRNT.Network.multistationarity_inherited_dependent`: the same statement for a network of
  *any* rank when the added reaction vectors lie in the stoichiometric subspace of the original
  network, the nondegeneracy being taken relative to that subspace.
* `CRNT.Network.nondegMultistationarity_inherited_union`: the nondegenerate form of the
  full-rank theorem — the enlarged network is *nondegenerately* multistationary.
* `CRNT.Network.TwoRxnIsAtom`, `CRNT.Network.twoRxnOpen_isAtom_iff`: the notion of an atom for
  the two-reaction fully open family, and its criterion in terms of the two one-reaction sums.
* The campaign's proof that the two-reaction criterion is a *complete decision procedure* on the
  75-member two-species family (`CRNT.Network.twoRxnMultistationary_complete`,
  `CRNT.Network.twoReaction_criterionTable_complete`, `CRNT.Network.twoReaction_atomTable_complete`).

All of these are stated for the *concrete* data (two steady states, their Jacobians).  The
*capacity* form — the statement in terms of the property `HasMultistationarityCapacity` — was
missing, and it is the capacity form that the atom theory needs.

## What this module adds

* `CRNT.Network.multistationarityCapacity_inherited_union`: **the multistationarity capacity is
  inherited by every enlargement** of a full-rank network that has two distinct nondegenerate
  positive steady states — for all sufficiently small rates of the added reactions the enlarged
  network `N ∪ M` *has the capacity* for multiple steady states.
* `CRNT.Network.multistationarityCapacity_inherited_union_dependent`: the same for a network of
  any rank when the added reactions are *dependent* (their reaction vectors lie in the
  stoichiometric subspace of `N`).
* `CRNT.Network.multistationarityCapacity_inherited_of_nondegenerate_capacity`: the capacity form
  with the hypothesis `N.HasNondegenerateMultistationarity` (the capacity of `N` together with
  the nondegeneracy of its two steady states).
* `CRNT.Network.nondegMultistationarityCapacity_inherited_union`: **the nondegenerate capacity is
  inherited by every enlargement** — for all sufficiently small rates the enlarged network is
  *nondegenerately* multistationary.  This uses `exists_nondegenerate_branches_range`, the
  neighbourhood version of the repository's `exists_nondegenerate_branches`.
* `CRNT.Network.twoRxnOpen_multistationary_of_oneRxn_multistationary` and
  `CRNT.Network.twoRxnOpen_not_atom_of_oneRxn_multistationary`: **a proper enlargement of a
  multistationary network is multistationary, and hence is not an atom** — in the two-reaction
  family, where the atom notion `TwoRxnIsAtom` is defined, adding the second reaction to a
  multistationary one-reaction fully open network keeps it multistationary and destroys the atom
  property.

## The hypothesis is not redundant: a counterexample

The capacity form *without* the full-rank and nondegeneracy hypotheses is **false**, and this
module proves the counterexample: `CRNT.Network.CapacityCounterExample` exhibits the network
`X + Y → 2X`, `2X + 2Y → X + 3Y` (whose two reaction vectors are `±(1, −1)`), which has the
capacity — the two steady states `(2, 1/2)` and `(1/2, 2)` are positive and lie in one
compatibility class — while the enlargement by the reaction `X → 2X`, whose reaction vector
`(1, 0)` leaves the stoichiometric subspace, has **no positive steady state at all**, for any
choice of rate constants.  The reason is structural: adding a reaction whose vector leaves the
stoichiometric subspace *increases* the number of independent steady-state equations, and the two
steady states of the original network need not survive.

## What remains open

* The *degenerate* capacity inheritance: the capacity of `N` (without nondegeneracy) is not
  inherited by an arbitrary enlargement — this module proves that this is false — but the case in
  which the stoichiometric subspace does not grow (the *dependent* case) is proved here only under
  the nondegeneracy relative to the class, which is the hypothesis the implicit function theorem
  needs.
* The atom theory beyond the two-reaction family: a general notion of an atom of multistationarity
  (with respect to the *embedded* relation, which also deletes species), and the catalog of the
  atoms of the small networks — the literature resolves these by computer-assisted enumeration,
  not by a closed-form criterion.
-/

namespace CRNT

namespace Network

open Filter Topology
open Finset
open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ### The capacity form of the inheritance of multistationarity -/

set_option linter.unusedVariables false in
/-- **The multistationarity capacity is inherited by every enlargement of a full-rank network.**
Two distinct positive *nondegenerate* steady states of `(N, κ)` persist, for all sufficiently
small rates of the added reactions, as two distinct positive steady states of `N ∪ M` in one
compatibility class; that is, `N ∪ M` *has the capacity* for multiple steady states.

This is the capacity form of `multistationarity_inherited_union` (Joshi–Shiu 2013, Theorem 3.1):
the conclusion is stated in terms of the property `HasMultistationarityCapacity` rather than in
terms of the two steady states, which is the form the theory of atoms needs. -/
theorem multistationarityCapacity_inherited_union (N M : Network S) (hS : N.stoichSubspace = ⊤)
    (κ : N.RateConstants) (κM : M.RateConstants) {x₁ x₂ : Concentration S}
    (hx₁ : x₁.Positive) (hx₂ : x₂.Positive) (hne : x₁ ≠ x₂)
    (hss₁ : N.IsMassActionSteadyState κ x₁) (hss₂ : N.IsMassActionSteadyState κ x₂)
    (hnd₁ : (fderiv ℝ (N.massActionVectorField κ) x₁).IsInvertible)
    (hnd₂ : (fderiv ℝ (N.massActionVectorField κ) x₂).IsInvertible) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε (hε : 0 < ε), ε < ε₀ →
      (N.union M).HasMultistationarityCapacity := by
  obtain ⟨ε₀, hε₀, h⟩ :=
    multistationarity_inherited_union N M κ κM hS hx₁ hx₂ hne hss₁ hss₂ hnd₁ hnd₂
  refine ⟨ε₀, hε₀, fun ε hε hεε => ?_⟩
  obtain ⟨y₁, y₂, p₁, p₂, hne', hcls, e₁, e₂⟩ := h ε hε hεε
  refine ⟨unionRates κ κM ε hε, y₁, y₁, y₂, ⟨?_, p₁⟩, ⟨?_, p₂⟩, e₁, e₂, hne'⟩
  · show y₁ - y₁ ∈ (N.union M).stoichSubspace
    rw [sub_self]; exact Submodule.zero_mem _
  · show y₂ - y₁ ∈ (N.union M).stoichSubspace
    have : y₂ - y₁ = -(y₁ - y₂) := by ring
    rw [this]
    exact (N.union M).stoichSubspace.neg_mem hcls

set_option linter.unusedVariables false in
/-- **The multistationarity capacity is inherited by every enlargement of a network of any rank
by *dependent* reactions.** Two distinct positive steady states of `(N, κ)` in one class, each
nondegenerate relative to the stoichiometric subspace of `N`, persist — for all sufficiently small
rates of the added reactions — as two distinct positive steady states of `N ∪ M` in one class,
whenever the reaction vectors of `M` lie in the stoichiometric subspace of `N`.

This is the capacity form of `multistationarity_inherited_dependent` (Joshi–Shiu 2013,
Theorem 3.1, lower-rank case). -/
theorem multistationarityCapacity_inherited_union_dependent (N M : Network S)
    (κ : N.RateConstants) (κM : M.RateConstants)
    (hdep : ∀ r : M.R, M.reactionVector r ∈ N.stoichSubspace)
    {x₁ x₂ : Concentration S} (hx₁ : x₁.Positive) (hx₂ : x₂.Positive) (hne : x₁ ≠ x₂)
    (hcls : x₁ - x₂ ∈ N.stoichSubspace)
    (hss₁ : N.IsMassActionSteadyState κ x₁) (hss₂ : N.IsMassActionSteadyState κ x₂)
    (hnd₁ : ∀ v ∈ N.stoichSubspace, N.massActionJacobianCLM κ x₁ v = 0 → v = 0)
    (hnd₂ : ∀ v ∈ N.stoichSubspace, N.massActionJacobianCLM κ x₂ v = 0 → v = 0) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε (hε : 0 < ε), ε < ε₀ →
      (N.union M).HasMultistationarityCapacity := by
  obtain ⟨ε₀, hε₀, h⟩ :=
    multistationarity_inherited_dependent N M κ κM hdep hx₁ hx₂ hne hcls hss₁ hss₂ hnd₁ hnd₂
  refine ⟨ε₀, hε₀, fun ε hε hεε => ?_⟩
  obtain ⟨y₁, y₂, p₁, p₂, hne', hcls', e₁, e₂⟩ := h ε hε hεε
  refine ⟨unionRates κ κM ε hε, y₁, y₁, y₂, ⟨?_, p₁⟩, ⟨?_, p₂⟩, e₁, e₂, hne'⟩
  · show y₁ - y₁ ∈ (N.union M).stoichSubspace
    rw [sub_self]; exact Submodule.zero_mem _
  · show y₂ - y₁ ∈ (N.union M).stoichSubspace
    have hneg : y₂ - y₁ = -(y₁ - y₂) := by ring
    rw [hneg]
    exact (stoichSubspace_le_union N M) ((N.stoichSubspace).neg_mem hcls')

set_option linter.unusedVariables false in
/-- **The capacity of a full-rank network is inherited by every enlargement.** If `N` is
*nondegenerately* multistationary — two distinct positive steady states in one class, both
nondegenerate — and `N` has full stoichiometric rank, then `N ∪ M` has the capacity for multiple
steady states for all sufficiently small rates of the added reactions.

This is the capacity form with the hypothesis stated in terms of the property
`HasNondegenerateMultistationarity`; the full-rank hypothesis is needed, and the nondegeneracy
is needed, as the counterexample `capacity_not_inherited_by_enlargement` shows. -/
theorem multistationarityCapacity_inherited_of_nondegenerate_capacity (N M : Network S)
    (hS : N.stoichSubspace = ⊤) (κM : M.RateConstants)
    (h : N.HasNondegenerateMultistationarity) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε (hε : 0 < ε), ε < ε₀ →
      (N.union M).HasMultistationarityCapacity := by
  obtain ⟨κ, x₀, x, y, hx, hy, hsx, hsy, hne, hndx, hndy⟩ := h
  exact multistationarityCapacity_inherited_union N M hS κ κM hx.2 hy.2 hne hsx hsy
    (isInvertible_of_nondegenerate hS hndx) (isInvertible_of_nondegenerate hS hndy)

/-! ### The nondegenerate capacity -/

set_option linter.unusedVariables false in
/-- **Two nondegenerate steady states persist on a whole interval of rates.** This is the
neighbourhood form of `exists_nondegenerate_branches`: for all sufficiently small `ε > 0` the
perturbed field has two distinct positive zeros with invertible Jacobians. -/
theorem exists_nondegenerate_branches_range (N M : Network S) (κ : N.RateConstants)
    (κM : M.RateConstants) {x z : Concentration S} (hx : x.Positive) (hz : z.Positive)
    (hne : x ≠ z) (hsx : N.IsMassActionSteadyState κ x) (hsz : N.IsMassActionSteadyState κ z)
    (hnx : (fderiv ℝ (N.massActionVectorField κ) x).IsInvertible)
    (hnz : (fderiv ℝ (N.massActionVectorField κ) z).IsInvertible) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε (hε : 0 < ε), ε < ε₀ →
      ∃ y₁ y₂ : Concentration S, y₁.Positive ∧ y₂.Positive ∧ y₁ ≠ y₂ ∧
        perturbedField N M κ κM (ε, y₁) = 0 ∧ perturbedField N M κ κM (ε, y₂) = 0 ∧
        (fderiv ℝ (fun y => perturbedField N M κ κM (ε, y)) y₁).IsInvertible ∧
        (fderiv ℝ (fun y => perturbedField N M κ κM (ε, y)) y₂).IsInvertible := by
  obtain ⟨ψ₁, h₁0, h₁c, h₁e⟩ := eventually_steadyState_branch N M κ κM hsx hnx
  obtain ⟨ψ₂, h₂0, h₂c, h₂e⟩ := eventually_steadyState_branch N M κ κM hsz hnz
  have hopen : IsOpen {y : S → ℝ | ∀ s, 0 < y s} := by
    have : {y : S → ℝ | ∀ s, 0 < y s} = ⋂ s, {y : S → ℝ | 0 < y s} := by ext; simp
    rw [this]
    exact isOpen_iInter_of_finite fun s => isOpen_lt continuous_const (continuous_apply s)
  have hpos₁ : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ s, 0 < ψ₁ ε s :=
    h₁c.preimage_mem_nhds (hopen.mem_nhds (by rw [h₁0]; exact hx))
  have hpos₂ : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ s, 0 < ψ₂ ε s :=
    h₂c.preimage_mem_nhds (hopen.mem_nhds (by rw [h₂0]; exact hz))
  have hsep : ∀ᶠ ε in 𝓝 (0 : ℝ), ψ₁ ε ≠ ψ₂ ε := by
    have h := h₁c.prodMk h₂c
    have hmem : {p : (S → ℝ) × (S → ℝ) | p.1 ≠ p.2} ∈ 𝓝 (ψ₁ 0, ψ₂ 0) := by
      refine isOpen_ne_fun continuous_fst continuous_snd |>.mem_nhds ?_
      rw [h₁0, h₂0]; exact hne
    exact h.preimage_mem_nhds hmem
  set D : ℝ × (S → ℝ) → (S → ℝ) →L[ℝ] (S → ℝ) := fun p =>
    fderiv ℝ (N.massActionVectorField κ) p.2 + p.1 • fderiv ℝ (M.massActionVectorField κM) p.2
    with hD
  have hDc : Continuous D := by
    have h1 := (N.contDiff_massActionVectorField κ).continuous_fderiv (by simp)
    have h2 := (M.contDiff_massActionVectorField κM).continuous_fderiv (by simp)
    exact (h1.comp continuous_snd).add (continuous_fst.smul (h2.comp continuous_snd))
  have hDeq : ∀ ε y, fderiv ℝ (fun y => perturbedField N M κ κM (ε, y)) y = D (ε, y) := by
    intro ε y
    have hN := ((N.contDiff_massActionVectorField κ).differentiable (by simp) y).hasFDerivAt
    have hM := ((M.contDiff_massActionVectorField κM).differentiable (by simp) y).hasFDerivAt
    exact (hN.add (hM.const_smul ε)).fderiv
  have hinv : ∀ (ψ : ℝ → S → ℝ) (x₀ : S → ℝ), ψ 0 = x₀ → ContinuousAt ψ 0 →
      (fderiv ℝ (N.massActionVectorField κ) x₀).IsInvertible →
      ∀ᶠ ε in 𝓝 (0 : ℝ), (D (ε, ψ ε)).IsInvertible := by
    intro ψ x₀ hψ0 hψc hx₀
    have hc : ContinuousAt (fun ε => D (ε, ψ ε)) 0 :=
      hDc.continuousAt.comp (continuousAt_id.prodMk hψc)
    have h0 : D (0, ψ 0) = fderiv ℝ (N.massActionVectorField κ) x₀ := by
      simp [hD, hψ0]
    have hmem : {T : (S → ℝ) →L[ℝ] (S → ℝ) | T.IsInvertible} ∈ 𝓝 (D (0, ψ 0)) := by
      rw [h0]; exact ContinuousLinearMap.isOpen_setOfPred_isInvertible.mem_nhds hx₀
    exact hc.preimage_mem_nhds hmem
  have hall := ((((h₁e.and h₂e).and (hpos₁.and hpos₂)).and hsep).and
    ((hinv ψ₁ x h₁0 h₁c hnx).and (hinv ψ₂ z h₂0 h₂c hnz)))
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hall
  refine ⟨δ, hδ, fun ε hε hεδ => ?_⟩
  have hdist : dist ε 0 < δ := by rw [Real.dist_eq, sub_zero, abs_of_pos hε]; exact hεδ
  obtain ⟨⟨⟨⟨e₁, e₂⟩, p₁, p₂⟩, hs⟩, i₁, i₂⟩ := hball hdist
  refine ⟨ψ₁ ε, ψ₂ ε, p₁, p₂, hs, e₁, e₂, ?_, ?_⟩
  · rw [hDeq]; exact i₁
  · rw [hDeq]; exact i₂

set_option linter.unusedVariables false in
/-- **The nondegenerate multistationarity capacity is inherited by every enlargement.** If `N`
has full stoichiometric rank and `(N, κ)` has two distinct positive steady states in one class,
both nondegenerate, then for all sufficiently small rates of the added reactions the enlarged
network `N ∪ M` is *nondegenerately* multistationary: it has two distinct positive steady states
in one class, both nondegenerate.

This is the nondegenerate capacity form of the inheritance; it is the neighbourhood version of
`nondegMultistationarity_inherited_union`, which produces a single rate. -/
theorem nondegMultistationarityCapacity_inherited_union (N M : Network S) (hS : N.stoichSubspace = ⊤)
    (κ : N.RateConstants) (κM : M.RateConstants) {x₁ x₂ : Concentration S}
    (hx₁ : x₁.Positive) (hx₂ : x₂.Positive) (hne : x₁ ≠ x₂)
    (hss₁ : N.IsMassActionSteadyState κ x₁) (hss₂ : N.IsMassActionSteadyState κ x₂)
    (hnd₁ : N.IsNondegenerateSteadyState κ x₁) (hnd₂ : N.IsNondegenerateSteadyState κ x₂) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε (hε : 0 < ε), ε < ε₀ →
      (N.union M).HasNondegenerateMultistationarity := by
  obtain ⟨ε₀, hε₀, h⟩ := exists_nondegenerate_branches_range N M κ κM hx₁ hx₂ hne hss₁ hss₂
    (isInvertible_of_nondegenerate hS hnd₁) (isInvertible_of_nondegenerate hS hnd₂)
  refine ⟨ε₀, hε₀, fun ε hε hεε => ?_⟩
  obtain ⟨y₁, y₂, p₁, p₂, hs, e₁, e₂, i₁, i₂⟩ := h ε hε hεε
  have hfield : (N.union M).massActionVectorField (unionRates κ κM ε hε) =
      fun y => perturbedField N M κ κM (ε, y) := by
    funext y
    rw [massActionVectorField_union]
    rfl
  have htop : (N.union M).stoichSubspace = ⊤ := eq_top_iff.mpr (hS ▸ stoichSubspace_le_union N M)
  refine ⟨unionRates κ κM ε hε, y₁, y₁, y₂, ⟨?_, p₁⟩, ⟨?_, p₂⟩, ?_, ?_, hs, ?_, ?_⟩
  · show y₁ - y₁ ∈ (N.union M).stoichSubspace
    rw [htop]; exact Submodule.mem_top
  · show y₂ - y₁ ∈ (N.union M).stoichSubspace
    rw [htop]; exact Submodule.mem_top
  · intro s; rw [hfield]; exact congrFun e₁ s
  · intro s; rw [hfield]; exact congrFun e₂ s
  · exact nondegenerate_of_isInvertible (by rw [hfield]; exact i₁)
  · exact nondegenerate_of_isInvertible (by rw [hfield]; exact i₂)

set_option linter.unusedVariables false in
/-- **The nondegenerate capacity of a full-rank network is inherited by every enlargement.** -/
theorem nondegMultistationarityCapacity_inherited_of_nondegenerate_capacity (N M : Network S)
    (hS : N.stoichSubspace = ⊤) (κM : M.RateConstants)
    (h : N.HasNondegenerateMultistationarity) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε (hε : 0 < ε), ε < ε₀ →
      (N.union M).HasNondegenerateMultistationarity := by
  obtain ⟨κ, x₀, x, y, hx, hy, hsx, hsy, hne, hndx, hndy⟩ := h
  exact nondegMultistationarityCapacity_inherited_union N M hS κ κM hx.2 hy.2 hne hsx hsy hndx hndy

/-! ### The two-reaction family: a proper enlargement is multistationary and is not an atom -/

/-- **The rate constants of the fully open two-reaction network built from the fully open
one-reaction network `a → b` (with rates `κ`) and the reaction `c → d` (with rates `ε κM`).** -/
def twoRxnOpenUnionRates (a b c d : Complex S) (κ : (oneRxn a b).fullyOpen.RateConstants)
    (κM : (oneRxn c d).RateConstants) (ε : ℝ) (hε : 0 < ε) :
    (twoRxnOpen a b c d).fullyOpen.RateConstants where
  k := Sum.elim
    (fun i : Fin 2 => if i = 0 then κ.k (Sum.inl ()) else ε * κM.k ())
    (Sum.elim (fun s => κ.k (Sum.inr (Sum.inl s))) (fun s => κ.k (Sum.inr (Sum.inr s))))
  positive := by
    intro r
    match r with
    | Sum.inl i =>
        show 0 < (if i = 0 then κ.k (Sum.inl ()) else ε * κM.k ())
        by_cases hi : i = 0
        · simp [hi]; exact κ.positive _
        · simp [hi]; exact mul_pos hε (κM.positive _)
    | Sum.inr (Sum.inl s) => exact κ.positive _
    | Sum.inr (Sum.inr s) => exact κ.positive _

/-- **The field of the union of the fully open one-reaction network with a one-reaction network is
the field of the fully open two-reaction network.** -/
theorem twoRxnOpen_field_eq_union (a b c d : Complex S)
    (κ : (oneRxn a b).fullyOpen.RateConstants) (κM : (oneRxn c d).RateConstants)
    (ε : ℝ) (hε : 0 < ε) (x : Concentration S) (s : S) :
    ((oneRxn a b).fullyOpen.union (oneRxn c d)).massActionVectorField
        (unionRates κ κM ε hε) x s =
      (twoRxnOpen a b c d).fullyOpen.massActionVectorField (twoRxnOpenUnionRates a b c d κ κM ε hε) x s := by
  rw [massActionVectorField_union]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [oneRxn_fullyOpen_field]
  rw [oneRxn_field]
  rw [twoRxnOpen_fullyOpen_field]
  simp [twoRxnOpenUnionRates]
  ring

set_option linter.unusedVariables false in
/-- **A proper enlargement of a multistationary network is multistationary.** If the fully open
one-reaction network `a → b` is multistationary, then the fully open two-reaction network
`a → b`, `c → d` — a proper enlargement of it — is multistationary as well: the second reaction
is added with a sufficiently small rate.

This is the lifting half of the atom theory of Joshi–Shiu in the two-reaction family: a
multistationary network can be enlarged, and the enlargement stays multistationary, so the
enlargement is not an atom (see `twoRxnOpen_not_atom_of_oneRxn_multistationary`). -/
theorem twoRxnOpen_multistationary_of_oneRxn_multistationary (a b c d : Complex S)
    (h : (oneRxn a b).fullyOpen.HasMultistationarityCapacity) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε (hε : 0 < ε), ε < ε₀ →
      (twoRxnOpen a b c d).fullyOpen.HasMultistationarityCapacity := by
  have hA : 1 < ∑ s ∈ univ.filter (fun s => a s < b s), a s :=
    (oneRxn_hasMultistationarityCapacity_iff a b).mp h
  have hnd : (oneRxn a b).fullyOpen.HasNondegenerateMultistationarity :=
    (oneRxn_nondegMultistationary_iff a b).mpr hA
  obtain ⟨κ, x₀, x, y, hx, hy, hsx, hsy, hne, hndx, hndy⟩ := hnd
  have hS : (oneRxn a b).fullyOpen.stoichSubspace = ⊤ :=
    stoichSubspace_fullyOpen_eq_top (oneRxn a b)
  obtain ⟨ε₀, hε₀, h⟩ :=
    multistationarity_inherited_union (oneRxn a b).fullyOpen (oneRxn c d) κ (oneRxnUnitRate c d)
      hS hx.2 hy.2 hne hsx hsy (isInvertible_of_nondegenerate hS hndx)
      (isInvertible_of_nondegenerate hS hndy)
  refine ⟨ε₀, hε₀, fun ε hε hεε => ?_⟩
  obtain ⟨y₁, y₂, p₁, p₂, hne', hcls, e₁, e₂⟩ := h ε hε hεε
  refine ⟨twoRxnOpenUnionRates a b c d κ (oneRxnUnitRate c d) ε hε, y₁, y₁, y₂, ⟨?_, p₁⟩, ⟨?_, p₂⟩,
    ?_, ?_, hne'⟩
  · show y₁ - y₁ ∈ (twoRxnOpen a b c d).fullyOpen.stoichSubspace
    rw [stoichSubspace_fullyOpen_eq_top]; exact Submodule.mem_top
  · show y₂ - y₁ ∈ (twoRxnOpen a b c d).fullyOpen.stoichSubspace
    rw [stoichSubspace_fullyOpen_eq_top]; exact Submodule.mem_top
  · intro s
    rw [← twoRxnOpen_field_eq_union a b c d κ (oneRxnUnitRate c d) ε hε y₁ s]
    exact e₁ s
  · intro s
    rw [← twoRxnOpen_field_eq_union a b c d κ (oneRxnUnitRate c d) ε hε y₂ s]
    exact e₂ s

/-- **A proper enlargement of a multistationary network is not an atom.** If the fully open
one-reaction network `a → b` is multistationary, then the fully open two-reaction network
`a → b`, `c → d` — which contains it as a proper subnetwork — is multistationary and hence is
*not* an atom of multistationarity (Joshi–Shiu 2013, Definition 5.1). -/
theorem twoRxnOpen_not_atom_of_oneRxn_multistationary (a b c d : Complex S)
    (h : (oneRxn a b).fullyOpen.HasMultistationarityCapacity) : ¬ TwoRxnIsAtom a b c d := by
  rintro ⟨hcap, h₁, h₂⟩
  exact h₁ h

/-! ### The capacity is *not* inherited by an arbitrary enlargement -/

/-
**A counterexample to the unrestricted capacity inheritance.** The network
`X + Y → 2X`, `2X + 2Y → X + 3Y` has the capacity for multiple steady states — the two steady
states `(2, 1/2)` and `(1/2, 2)` are positive and differ by a multiple of the reaction vector
`(1, −1)` — while its enlargement by the reaction `X → 2X`, whose reaction vector `(1, 0)` leaves
the stoichiometric subspace, has *no positive steady state at all*, for any choice of rate
constants.

Hence the hypotheses of `multistationarityCapacity_inherited_union` (full stoichiometric rank and
nondegeneracy) cannot be dropped: the statement "the capacity is inherited by every enlargement"
is false in general.
-/

namespace CapacityCounterExample

/-- The two species `X` (`false`) and `Y` (`true`). -/
abbrev Sp := Bool

/-- The complex `X`. -/
def cX : Complex Sp := fun s => if s then 0 else 1

/-- The complex `2X`. -/
def cTwoX : Complex Sp := fun s => if s then 0 else 2

/-- The complex `X + Y`. -/
def cXY : Complex Sp := fun _ => 1

/-- The complex `2X + 2Y`. -/
def cTwoXY : Complex Sp := fun _ => 2

/-- The complex `X + 3Y`. -/
def cXThreeY : Complex Sp := fun s => if s then 3 else 1

/-- The network `X + Y → 2X`, `2X + 2Y → X + 3Y`.  Both reaction vectors are `±(1, −1)`. -/
abbrev net : Network Sp := ⟨Fin 2, inferInstance, inferInstance,
  fun r => if r = 0 then ⟨cXY, cTwoX⟩ else ⟨cTwoXY, cXThreeY⟩⟩

/-- The network `X → 2X`, whose reaction vector `(1, 0)` leaves the stoichiometric subspace of
`net`. -/
abbrev extra : Network Sp := ⟨Fin 1, inferInstance, inferInstance, fun _ => ⟨cX, cTwoX⟩⟩

/-- The reaction vector of the first reaction of `net` is `(1, −1)`. -/
theorem net_reactionVector_zero (s : Sp) :
    net.reactionVector (0 : Fin 2) s = if s then (-1 : ℝ) else 1 := by
  rw [reactionVector_apply]
  cases s <;> simp [cXY, cTwoX]
  all_goals norm_num

/-- The field of `net`. -/
theorem net_field (κ : net.RateConstants) (p : Concentration Sp) (s : Sp) :
    net.massActionVectorField κ p s =
      (κ.k (0 : Fin 2) * (p false * p true) - κ.k (1 : Fin 2) * (p false * p true)^2) *
        (if s then (-1 : ℝ) else 1) := by
  rw [massActionVectorField_apply, Fin.sum_univ_two]
  simp only [massActionRate]
  cases s <;> simp [net, Complex.massActionMonomial, cXY, cTwoX, cTwoXY, cXThreeY]
  all_goals ring

/-- The field of `extra`. -/
theorem extra_field (κ : extra.RateConstants) (p : Concentration Sp) (s : Sp) :
    extra.massActionVectorField κ p s =
      κ.k (0 : Fin 1) * p false * (if s then (0 : ℝ) else 1) := by
  rw [massActionVectorField_apply, Fin.sum_univ_one]
  simp only [massActionRate]
  cases s <;> simp [extra, Complex.massActionMonomial, cX, cTwoX]
  all_goals ring

/-- The unit rate constants of `net`. -/
def netRates : net.RateConstants := ⟨fun _ => 1, fun _ => one_pos⟩

/-- The unit rate constants of `extra`. -/
def extraRates : extra.RateConstants := ⟨fun _ => 1, fun _ => one_pos⟩

/-- The field of the union `net ∪ extra`. -/
theorem union_field (κU : (net.union extra).RateConstants) (p : Concentration Sp) (s : Sp) :
    (net.union extra).massActionVectorField κU p s =
      (κU.k (Sum.inl (0 : Fin 2)) * (p false * p true) -
          κU.k (Sum.inl (1 : Fin 2)) * (p false * p true)^2) * (if s then (-1 : ℝ) else 1) +
        κU.k (Sum.inr (0 : Fin 1)) * p false * (if s then (0 : ℝ) else 1) := by
  rw [massActionVectorField_apply]
  show (∑ r : net.R ⊕ extra.R, (net.union extra).massActionRate κU r p *
      (net.union extra).reactionVector r s) = _
  rw [Fintype.sum_sum_type]
  simp only [massActionRate]
  rw [Fin.sum_univ_two, Fin.sum_univ_one]
  cases s <;>
    simp [union, net, extra, Complex.massActionMonomial, cXY, cTwoX, cTwoXY, cXThreeY, cX]
  all_goals ring

/-- The steady state `(2, 1/2)`. -/
noncomputable def st₁ : Concentration Sp := fun s => if s then (1 / 2 : ℝ) else 2

/-- The steady state `(1/2, 2)`. -/
noncomputable def st₂ : Concentration Sp := fun s => if s then 2 else (1 / 2 : ℝ)

theorem st₁_pos : st₁.Positive := by
  intro s; cases s <;> simp [st₁]

theorem st₂_pos : st₂.Positive := by
  intro s; cases s <;> simp [st₂]

theorem st₁_ne_st₂ : st₁ ≠ st₂ := by
  intro h
  have this := congrFun h false
  simp [st₁, st₂] at this
  norm_num at this

theorem st₁_prod : st₁ false * st₁ true = 1 := by
  simp [st₁]

theorem st₂_prod : st₂ false * st₂ true = 1 := by
  simp [st₂]

theorem st₁_steadyState : net.IsMassActionSteadyState netRates st₁ := by
  intro s
  rw [net_field, st₁_prod]
  simp [netRates]

theorem st₂_steadyState : net.IsMassActionSteadyState netRates st₂ := by
  intro s
  rw [net_field, st₂_prod]
  simp [netRates]

theorem st₂_sub_st₁_mem : st₂ - st₁ ∈ net.stoichSubspace := by
  have h : st₂ - st₁ = (-3 / 2 : ℝ) • net.reactionVector (0 : Fin 2) := by
    funext s
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [net_reactionVector_zero]
    cases s <;> simp [st₁, st₂] <;> ring
  rw [h]
  exact net.stoichSubspace.smul_mem _ (net.reactionVector_mem_stoichSubspace (0 : Fin 2))

/-- **The network `net` has the capacity for multiple steady states.** -/
theorem net_hasCapacity : net.HasMultistationarityCapacity := by
  refine ⟨netRates, st₁, st₁, st₂, ⟨StoichCompatible.refl _ _, st₁_pos⟩,
    ⟨?_, st₂_pos⟩, st₁_steadyState, st₂_steadyState, st₁_ne_st₂⟩
  show st₂ - st₁ ∈ net.stoichSubspace
  exact st₂_sub_st₁_mem

/-- **The enlargement has no positive steady state at all, for any rate constants.** -/
theorem union_no_positive_steadyState (κU : (net.union extra).RateConstants) :
    ¬ ∃ x : Concentration Sp, x.Positive ∧
        (net.union extra).IsMassActionSteadyState κU x := by
  rintro ⟨x, hx, hss⟩
  have h1 := hss true
  rw [union_field] at h1
  have h1' : κU.k (Sum.inl (0 : Fin 2)) * (x false * x true) -
      κU.k (Sum.inl (1 : Fin 2)) * (x false * x true)^2 = 0 := by
    simp at h1
    linarith
  have h2 := hss false
  rw [union_field] at h2
  simp at h2
  rw [h1'] at h2
  have hzero : κU.k (Sum.inr (0 : Fin 1)) * x false = 0 := by nlinarith [h2]
  rcases mul_eq_zero.mp hzero with h | h
  · exact absurd h (κU.positive (Sum.inr (0 : Fin 1))).ne'
  · exact absurd h (hx false).ne'

set_option linter.unusedVariables false in
/-- **The multistationarity capacity is *not* inherited by an arbitrary enlargement.** -/
theorem capacity_not_inherited_by_enlargement :
    ∃ (N M : Network Sp) (κ : N.RateConstants) (κM : M.RateConstants),
      N.HasMultistationarityCapacity ∧
        (∀ ε : ℝ, (0 : ℝ) < ε → ¬ (N.union M).HasMultistationarityCapacity) ∧
        (∀ κU : (N.union M).RateConstants, ¬ ∃ x : Concentration Sp, x.Positive ∧
          (N.union M).IsMassActionSteadyState κU x) := by
  refine ⟨net, extra, netRates, extraRates, net_hasCapacity, ?_, ?_⟩
  · intro ε hε hcap
    obtain ⟨κU, x₀, x, y, hx, hy, hsx, hsy, hne⟩ := hcap
    exact union_no_positive_steadyState κU ⟨x, hx.2, hsx⟩
  · intro κU
    exact union_no_positive_steadyState κU

end CapacityCounterExample

/-! ### A concrete instance -/

namespace ConcreteInstance

/-- The two species `X` (`false`) and `Y` (`true`). -/
abbrev Sp := Bool

/-- The complex `X`. -/
def cX : Complex Sp := fun s => if s then 0 else 1

/-- The complex `2X`. -/
def cTwoX : Complex Sp := fun s => if s then 0 else 2

/-- The complex `3X`. -/
def cThreeX : Complex Sp := fun s => if s then 0 else 3

/-- **The fully open one-reaction network `2X → 3X` is multistationary.** Indeed
`∑_{i : b_i > a_i} a_i = 2 > 1`, so Joshi's criterion applies. -/
theorem oneRxn_multistationary : (oneRxn cTwoX cThreeX).fullyOpen.HasMultistationarityCapacity := by
  rw [oneRxn_hasMultistationarityCapacity_iff]
  decide

/-- **The fully open two-reaction network `2X → 3X`, `X → 2X` — the enlargement of the
multistationary one-reaction network — is multistationary.** -/
theorem twoRxn_multistationary :
    (twoRxnOpen cTwoX cThreeX cX cTwoX).fullyOpen.HasMultistationarityCapacity := by
  have hex := twoRxnOpen_multistationary_of_oneRxn_multistationary cTwoX cThreeX cX cTwoX
    oneRxn_multistationary
  have hpos : 0 < hex.choose := hex.choose_spec.1
  exact hex.choose_spec.2 (hex.choose / 2) (by positivity) (by linarith)

/-- **The enlargement is not an atom of multistationarity.** -/
theorem twoRxn_not_atom : ¬ TwoRxnIsAtom cTwoX cThreeX cX cTwoX :=
  twoRxnOpen_not_atom_of_oneRxn_multistationary cTwoX cThreeX cX cTwoX oneRxn_multistationary

end ConcreteInstance

end Network

end CRNT

/-! ### The principal declarations -/

#print axioms CRNT.Network.multistationarityCapacity_inherited_union
#print axioms CRNT.Network.multistationarityCapacity_inherited_union_dependent
#print axioms CRNT.Network.multistationarityCapacity_inherited_of_nondegenerate_capacity
#print axioms CRNT.Network.nondegMultistationarityCapacity_inherited_union
#print axioms CRNT.Network.nondegMultistationarityCapacity_inherited_of_nondegenerate_capacity
#print axioms CRNT.Network.twoRxnOpen_multistationary_of_oneRxn_multistationary
#print axioms CRNT.Network.twoRxnOpen_not_atom_of_oneRxn_multistationary
#print axioms CRNT.Network.ConcreteInstance.twoRxn_multistationary
#print axioms CRNT.Network.ConcreteInstance.twoRxn_not_atom
#print axioms CRNT.Network.CapacityCounterExample.capacity_not_inherited_by_enlargement
