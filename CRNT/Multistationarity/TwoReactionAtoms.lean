import CRNT.Multistationarity.Capacity
import CRNT.Multistationarity.OneReactionExistence
import CRNT.Multistationarity.OneReactionReversibleUnique
import CRNT.Open.Augmentation

/-!
# Two-reaction atoms of multistationarity (Joshi–Shiu 2013)

This module treats the two-reaction part of the catalog of **atoms of multistationarity** for
fully open networks, i.e. of the CFSTRs of Joshi and Shiu, *Atoms of multistationarity in
chemical reaction networks*, J. Math. Chem. 51 (2013), 153–178.  It proves the atom criterion
for two-reaction fully open networks, settles the reversible-pair case, records how the
possible shapes of the two reaction vectors interact, and gives three concrete instances —
an atom, a crossing pair that is never multistationary, and a multistationary pair that does
not cross.  The general multistationarity criterion for two irreversible reactions is *not*
available in closed form in the literature (see "What is still missing" below).

## Background

A **fully open network** (`N.fullyOpen`, see `CRNT.Open.Augmentation`) adjoins to a network `N`
the flow reactions `0 → s` (inflows) and `s → 0` (outflows) for every species `s`; its
stoichiometric subspace is the whole space, so all positive concentrations lie in one
compatibility class. A fully open network is **multistationary** when some choice of positive
rate constants admits two distinct positive steady states (`HasMultistationarityCapacity`).

Following Joshi–Shiu (Definition 5.1), a fully open network is an **atom of multistationarity**
when it is multistationary and *minimal*: no proper (fully open) subnetwork of it is
multistationary. With respect to the *subnetwork* relation (delete reactions, keep the
species) the proper subnetworks of a two-reaction fully open network are obtained by deleting
one of the two non-flow reactions; deleting both leaves the purely linear flow network, which
always has a unique positive steady state.

## What the repository already contains

* `CRNT.Network.oneRxn_multistationary_iff` (Joshi 2013, Theorem 4.1): the fully open network
  with the single non-flow reaction `a → b` is multistationary iff `∑_{i : b_i > a_i} a_i > 1`;
  `oneRxn_unique_steadyState` is the "only if" half, `oneRxn_nondegMultistationary_iff` the
  nondegenerate form.
* `CRNT.Network.revPair_multistationary_iff` (Joshi 2013, Theorem 4.1(2)): the fully open
  network with the reversible non-flow reaction `a ⇌ b` is multistationary iff
  `∑_{i : b_i > a_i} a_i > 1` or `∑_{i : a_i > b_i} b_i > 1`.
* `CRNT.Network.multistationarity_inherited_fullyOpen_union` and
  `multistationarity_inherited_addSpecies` (Joshi–Shiu 2013, Theorems 3.1 and 4.2): the
  *lifting* half of the theory — multistationarity of a subnetwork is inherited by a larger
  fully open network. Together with Joshi–Shiu's Corollary 5.2 this is what makes the catalog
  of atoms meaningful.
* The *closed* two-reaction networks (without flow reactions): `CRNT.Network.twoRxn` with
  `twoRxn_multistationary_iff` (Joshi–Shiu 2017, Theorem 5.1), `revIrr_multistationary_iff`
  (Theorem 5.8) and `revRev_multistationary_iff` (Theorem 5.12). These concern the closed
  networks and are not the fully open two-reaction case treated here.

## What this module adds

* `twoRxnOpen` — the two-reaction network `a → b`, `c → d` — and `twoRxnOpen_fullyOpen_field`,
  the explicit mass-action field of its fully open extension.
* `fullyOpen_hasMultistationarityCapacity_iff` and `oneRxn_hasMultistationarityCapacity_iff`:
  for a fully open network the capacity is the existence of two distinct positive steady
  states, and for the one-reaction network it is Joshi's criterion.
* `oneRxn_monostationary_iff`: the one-reaction network is *monostationary* (at most one
  positive steady state for **every** choice of rate constants) iff `∑_{i : b_i > a_i} a_i ≤ 1`.
* `emptyNet`, `emptyNet_fullyOpen_field` and `emptyNet_unique_steadyState`: the fully open
  network *without* non-flow reactions is monostationary, so that the flow-only subnetwork of a
  two-reaction fully open network never spoils the atom property.
* **`twoRxnOpen_isAtom_iff`: the two-reaction atom criterion.** The fully open extension of
  `a → b`, `c → d` is an atom of multistationarity iff it is multistationary and
  `∑_{i : b_i > a_i} a_i ≤ 1` and `∑_{i : d_i > c_i} c_i ≤ 1` — that is, iff it is
  multistationary and neither of its one-reaction subnetwork extensions is multistationary
  (Joshi 2013, Theorem 4.1, in the "only if" direction).
* **The reversible pair.** `twoRxnOpen_revPair_multistationary_iff` gives the multistationarity
  criterion for the pair `a ⇌ b` (the two reactions being each other's reverse), and
  `twoRxnOpen_revPair_not_atom` shows that a reversible pair is **never** an atom: whenever it
  is multistationary, one of the two single reactions is multistationary as well.
* **The shape of the two reaction vectors.** `Crosses` (the vectors change sign against each
  other), `VectorsIndependent` (the vectors are neither positive multiples nor opposites),
  `ReactionsParallel`; `crossing_not_parallel`, `revPair_crosses_iff`,
  `revPair_not_independent`, `independent_reactions` and `parallel_not_independent` record how
  these notions interact.  **A remark on independence:** the two reaction vectors of a
  reversible pair are *opposite* multiples of one another, so the hypothesis "neither vector is
  a positive multiple of the other" does *not* by itself exclude the reversible-pair case; the
  notion of independence used here (`VectorsIndependent`) excludes positive multiples *and*
  opposites, and `independent_reactions` then yields "neither a reversible pair nor
  parallel".
* **Three concrete instances.**
  * `TwoReactionAtomExample.atom_isAtom`: the network `X + Y → 3X`, `2X + Y → X + 2Y` (reaction
    vectors `(2, −1)` and `(−1, 1)`, which cross and are independent) is an atom of
    multistationarity; the two steady states `(1, 1)` and `(1/3, 1/3)` and the rate constants are
    given explicitly.
  * `TwoReactionAtomExample.crossNet_not_multistationary`: the network `X + Y → 2X`,
    `X + Y → 2Y` has **crossing** reaction vectors `(1, −1)` and `(−1, 1)` but is **never**
    multistationary: it has at most one positive steady state for every choice of rate
    constants. Hence the "crossing condition" alone does *not* characterise multistationarity
    of a fully open two-reaction network.
  * `TwoReactionAtomExample.parallel_multistationary` and `parallel_not_crosses`: the network
    `X → 2X`, `2Y → 3Y` (reaction vectors `(1, 0)` and `(0, 1)`) is multistationary although its
    reaction vectors do **not** cross — the reaction `2Y → 3Y` is multistationary on its own.
    Hence the "non-crossing condition" does *not* rule out multistationarity either.

## What is still missing

The full two-reaction classification of Joshi–Shiu (2013), Theorem 7.1, is a *finite
enumeration*: of the 386 reversible bimolecular two-reaction fully open CFSTRs exactly 35 are
multistationary, each contains a unique minimal multistationary sub-CFSTR, and these form a
poset with 11 minimal elements — the bimolecular two-reaction atoms of multistationarity. The
enumeration is computer-assisted (CRN Toolbox) and has **no closed-form criterion** in the
literature; in particular there is no general necessary-and-sufficient condition on the two
reaction vectors `w₁`, `w₂` of the kind "the network is multistationary iff `w₁` and `w₂`
cross".

This module therefore proves the exact part of the two-reaction story that is available in
closed form:

* the **atom criterion** `twoRxnOpen_isAtom_iff`: the atom property of a two-reaction fully
  open network is completely determined by the two one-reaction sums
  `∑_{i : b_i > a_i} a_i` and `∑_{i : d_i > c_i} c_i` together with the multistationarity of
  the two-reaction network itself;
* the **reversible pair** case, in full;
* the **structural facts** about crossing, independence and parallelism;
* three **concrete instances**: an atom with crossing reaction vectors, a crossing pair that is
  never multistationary, and a multistationary pair whose vectors do not cross.

The remaining item is the *general multistationarity criterion for two irreversible reactions
with independent reaction vectors* (the "if and only if" part of
`twoRxnOpen_isAtom_iff`): one would need, for arbitrary `a → b` and `c → d`, a necessary and
sufficient condition on `(a, b, c, d)` for the fully open two-reaction network to have two
distinct positive steady states. The obstruction is that this condition is not a condition on
the reaction vectors alone: the examples above show that the same *sign pattern* of the
reaction vectors can be multistationary or not, depending on the source multiplicities (the
pairs `(1, −1), (−1, 1)` and `(2, −1), (−1, 1)` behave differently), and the literature
resolves the small case by computer-assisted enumeration rather than by a formula.

Two further items are deliberately left out of this module.

* The *embedded* version of the atom notion.  Joshi–Shiu define an atom of multistationarity
  to be minimal with respect to the **embedded** network relation, which also allows deleting
  *species*; the criterion `twoRxnOpen_isAtom_iff` uses the weaker **subnetwork** relation
  (delete reactions, keep the species), which is the notion asked for here.  For the one-reaction
  network the two notions differ: the embedded one is characterised in Joshi–Shiu (2013),
  Corollary 5.3, by the two shapes `a₁ X → a₂ X` (`a₂ > a₁ > 1`) and `X + Y → b₁ X + b₂ Y`
  (`b₁, b₂ > 1`); it would follow from `oneRxn_monostationary_iff` once the species-deletion
  relation is related to the one-reaction criterion.
* The **nondegeneracy** of the two steady states of the atom of
  `TwoReactionAtomExample.atom_isAtom` (the repository has the nondegenerate one-reaction
  criterion `oneRxn_nondegMultistationary_iff`, but no two-reaction analogue).
-/

namespace CRNT

namespace Network

open Finset
open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The network with the two non-flow reactions `a → b` (index `0`) and `c → d` (index `1`). -/
abbrev twoRxnOpen (a b c d : Complex S) : Network S :=
  ⟨Fin 2, inferInstance, inferInstance, fun r => if r = 0 then ⟨a, b⟩ else ⟨c, d⟩⟩

theorem twoRxnOpen_fullyOpen_field (a b c d : Complex S)
    (κ : (twoRxnOpen a b c d).fullyOpen.RateConstants) (x : Concentration S) (s : S) :
    (twoRxnOpen a b c d).fullyOpen.massActionVectorField κ x s =
      κ.k (Sum.inl (0 : Fin 2)) * a.massActionMonomial x * ((b s : ℝ) - a s) +
        κ.k (Sum.inl (1 : Fin 2)) * c.massActionMonomial x * ((d s : ℝ) - c s) +
        κ.k (Sum.inr (Sum.inl s)) - κ.k (Sum.inr (Sum.inr s)) * x s := by
  have hrin : ((twoRxnOpen a b c d).fullyOpen.reaction (Sum.inr (Sum.inl s))) = inflowReaction s := rfl
  have hrout : ((twoRxnOpen a b c d).fullyOpen.reaction (Sum.inr (Sum.inr s))) = outflowReaction s := rfl
  rw [massActionVectorField_apply]
  erw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [massActionRate]
  have h1 : (∑ r : (twoRxnOpen a b c d).R, κ.k (Sum.inl r) *
      ((twoRxnOpen a b c d).fullyOpen.reaction (Sum.inl r)).source.massActionMonomial x *
        (twoRxnOpen a b c d).fullyOpen.reactionVector (Sum.inl r) s) =
      κ.k (Sum.inl (0 : Fin 2)) * a.massActionMonomial x * ((b s : ℝ) - a s) +
        κ.k (Sum.inl (1 : Fin 2)) * c.massActionMonomial x * ((d s : ℝ) - c s) := by
    rw [Fin.sum_univ_two]
    rfl
  have h2 : (∑ s' : S, κ.k (Sum.inr (Sum.inl s')) *
      ((twoRxnOpen a b c d).fullyOpen.reaction (Sum.inr (Sum.inl s'))).source.massActionMonomial x *
        (twoRxnOpen a b c d).fullyOpen.reactionVector (Sum.inr (Sum.inl s')) s) =
      κ.k (Sum.inr (Sum.inl s)) := by
    rw [Finset.sum_eq_single s (fun s' _ hs' => by
      erw [reactionVector_inflow]; simp [Ne.symm hs']) (by simp)]
    erw [reactionVector_inflow, hrin]
    simp [inflowReaction]
  have h3 : (∑ s' : S, κ.k (Sum.inr (Sum.inr s')) *
      ((twoRxnOpen a b c d).fullyOpen.reaction (Sum.inr (Sum.inr s'))).source.massActionMonomial x *
        (twoRxnOpen a b c d).fullyOpen.reactionVector (Sum.inr (Sum.inr s')) s) =
      -(κ.k (Sum.inr (Sum.inr s)) * x s) := by
    rw [Finset.sum_eq_single s (fun s' _ hs' => by
      erw [reactionVector_outflow]; simp [Ne.symm hs']) (by simp)]
    erw [reactionVector_outflow, hrout]
    simp [outflowReaction, Complex.massActionMonomial, singletonComplex, Pi.single_apply]
  rw [h1, h2, h3]; ring

/-! ### The capacity of a fully open network -/

/-- In a fully open network every two concentrations are stoichiometrically compatible: the
stoichiometric subspace of the fully open extension is the whole space. -/
theorem fullyOpen_stoichCompatible (N : Network S) (x y : Concentration S) :
    N.fullyOpen.StoichCompatible x y := by
  show y - x ∈ N.fullyOpen.stoichSubspace
  rw [stoichSubspace_fullyOpen_eq_top]
  exact Submodule.mem_top

/-- **The capacity of a fully open network.** A fully open network has the capacity for multiple
steady states iff some choice of positive rate constants admits two distinct positive steady
states (they are automatically in one compatibility class). -/
theorem fullyOpen_hasMultistationarityCapacity_iff (N : Network S) :
    N.fullyOpen.HasMultistationarityCapacity ↔
      ∃ (κ : N.fullyOpen.RateConstants) (x z : Concentration S),
        x.Positive ∧ z.Positive ∧ x ≠ z ∧
          N.fullyOpen.IsMassActionSteadyState κ x ∧ N.fullyOpen.IsMassActionSteadyState κ z := by
  constructor
  · rintro ⟨κ, x₀, x, z, hx, hz, hsx, hsz, hne⟩
    exact ⟨κ, x, z, hx.2, hz.2, hne, hsx, hsz⟩
  · rintro ⟨κ, x, z, hx, hz, hne, hsx, hsz⟩
    refine ⟨κ, x, x, z, ⟨fullyOpen_stoichCompatible N x x, hx⟩,
      ⟨fullyOpen_stoichCompatible N x z, hz⟩, hsx, hsz, hne⟩

/-- **Joshi 2013, Theorem 4.1, in the fully open form.** The fully open network with the single
non-flow reaction `a → b` has the capacity for multiple steady states iff
`∑_{i : b_i > a_i} a_i > 1`. -/
theorem oneRxn_hasMultistationarityCapacity_iff (a b : Complex S) :
    (oneRxn a b).fullyOpen.HasMultistationarityCapacity ↔
      1 < ∑ s ∈ univ.filter (fun s => a s < b s), a s := by
  rw [fullyOpen_hasMultistationarityCapacity_iff]
  exact oneRxn_multistationary_iff a b

/-- **A one-reaction network is monostationary iff `∑_{i : b_i > a_i} a_i ≤ 1`.** Here
*monostationary* means that every choice of positive rate constants admits at most one positive
steady state. -/
theorem oneRxn_monostationary_iff (a b : Complex S) :
    (∀ (κ : (oneRxn a b).fullyOpen.RateConstants) (x z : Concentration S) (_hx : x.Positive)
        (_hz : z.Positive), (oneRxn a b).fullyOpen.IsMassActionSteadyState κ x →
        (oneRxn a b).fullyOpen.IsMassActionSteadyState κ z → x = z) ↔
      (∑ s ∈ univ.filter (fun s => a s < b s), a s) ≤ 1 := by
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    obtain ⟨κ, x, z, hx, hz, hne, hsx, hsz⟩ := (oneRxn_multistationary_iff a b).mpr hcon
    exact hne (h κ x z hx hz hsx hsz)
  · intro hA κ x z hx hz hsx hsz
    exact oneRxn_unique_steadyState a b hA κ hx hz hsx hsz

/-! ### The network without non-flow reactions -/

/-- The network with no non-flow reaction at all. -/
abbrev emptyNet : Network S := ⟨Empty, inferInstance, inferInstance, Empty.elim⟩

/-- **The field of the fully open network without non-flow reactions.** -/
theorem emptyNet_fullyOpen_field (κ : emptyNet.fullyOpen.RateConstants) (x : Concentration S)
    (s : S) :
    emptyNet.fullyOpen.massActionVectorField κ x s =
      κ.k (Sum.inr (Sum.inl s)) - κ.k (Sum.inr (Sum.inr s)) * x s := by
  have hrin : (emptyNet.fullyOpen.reaction (Sum.inr (Sum.inl s))) = inflowReaction s := rfl
  have hrout : (emptyNet.fullyOpen.reaction (Sum.inr (Sum.inr s))) = outflowReaction s := rfl
  rw [massActionVectorField_apply]
  erw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [massActionRate]
  have h1 : (∑ r : emptyNet.R, κ.k (Sum.inl r) *
      (emptyNet.fullyOpen.reaction (Sum.inl r)).source.massActionMonomial x *
        emptyNet.fullyOpen.reactionVector (Sum.inl r) s) = 0 := by
    exact Finset.sum_eq_zero fun r _ => nomatch r
  have h2 : (∑ s' : S, κ.k (Sum.inr (Sum.inl s')) *
      (emptyNet.fullyOpen.reaction (Sum.inr (Sum.inl s'))).source.massActionMonomial x *
        emptyNet.fullyOpen.reactionVector (Sum.inr (Sum.inl s')) s) = κ.k (Sum.inr (Sum.inl s)) := by
    rw [Finset.sum_eq_single s (fun s' _ hs' => by
      erw [reactionVector_inflow]; simp [Ne.symm hs']) (by simp)]
    erw [reactionVector_inflow, hrin]
    simp [inflowReaction]
  have h3 : (∑ s' : S, κ.k (Sum.inr (Sum.inr s')) *
      (emptyNet.fullyOpen.reaction (Sum.inr (Sum.inr s'))).source.massActionMonomial x *
        emptyNet.fullyOpen.reactionVector (Sum.inr (Sum.inr s')) s) =
      -(κ.k (Sum.inr (Sum.inr s)) * x s) := by
    rw [Finset.sum_eq_single s (fun s' _ hs' => by
      erw [reactionVector_outflow]; simp [Ne.symm hs']) (by simp)]
    erw [reactionVector_outflow, hrout]
    simp [outflowReaction, Complex.massActionMonomial, singletonComplex, Pi.single_apply]
  rw [h1, h2, h3]; ring

/-- **The fully open network without non-flow reactions is monostationary**: it has at most one
positive steady state for every choice of rate constants.  Deleting both non-flow reactions of
a two-reaction fully open network therefore never spoils the atom property. -/
theorem emptyNet_unique_steadyState (κ : emptyNet.fullyOpen.RateConstants) {x z : Concentration S}
    (_hx : x.Positive) (_hz : z.Positive)
    (hxs : emptyNet.fullyOpen.IsMassActionSteadyState κ x)
    (hzs : emptyNet.fullyOpen.IsMassActionSteadyState κ z) : x = z := by
  funext s
  have h1 := hxs s
  have h2 := hzs s
  rw [emptyNet_fullyOpen_field] at h1 h2
  have hl := κ.positive (Sum.inr (Sum.inr s))
  have h3 : κ.k (Sum.inr (Sum.inr s)) * x s = κ.k (Sum.inr (Sum.inr s)) * z s := by linarith
  exact mul_left_cancel₀ hl.ne' h3

/-! ### Atoms of multistationarity for two reactions -/

/-- The fully open extension of the two-reaction network `a → b`, `c → d` is an **atom of
multistationarity** (Joshi–Shiu 2013, Definition 5.1) when it is multistationary and no proper
fully open subnetwork of it is multistationary.

With respect to the *subnetwork* relation (which deletes reactions but keeps all species) the
proper subnetwork of a two-reaction fully open network is obtained by deleting one of the two
non-flow reactions: the two one-reaction fully open networks. Deleting both non-flow reactions
leaves the purely linear flow network, which always has a unique positive steady state
(`emptyNet_unique_steadyState`). Hence the condition below is exactly "multistationary, and every
proper subnetwork is monostationary". -/
def TwoRxnIsAtom (a b c d : Complex S) : Prop :=
  (twoRxnOpen a b c d).fullyOpen.HasMultistationarityCapacity ∧
    ¬ (oneRxn a b).fullyOpen.HasMultistationarityCapacity ∧
    ¬ (oneRxn c d).fullyOpen.HasMultistationarityCapacity

/-- **The two-reaction atom criterion.** The fully open extension of the two-reaction network
`a → b`, `c → d` is an atom of multistationarity iff it is multistationary and neither of its
one-reaction subnetwork extensions is multistationary, i.e. iff

* it is multistationary, and
* `∑_{i : b_i > a_i} a_i ≤ 1` and `∑_{i : d_i > c_i} c_i ≤ 1`.

The two numerical conditions are the one-reaction criterion of Joshi 2013, Theorem 4.1, read in
the "only if" direction. -/
theorem twoRxnOpen_isAtom_iff (a b c d : Complex S) :
    TwoRxnIsAtom a b c d ↔
      (twoRxnOpen a b c d).fullyOpen.HasMultistationarityCapacity ∧
        (∑ s ∈ univ.filter (fun s => a s < b s), a s) ≤ 1 ∧
        (∑ s ∈ univ.filter (fun s => c s < d s), c s) ≤ 1 := by
  constructor
  · rintro ⟨hcap, h₁, h₂⟩
    refine ⟨hcap, ?_, ?_⟩
    · by_contra hcon
      push Not at hcon
      exact h₁ ((oneRxn_hasMultistationarityCapacity_iff a b).mpr hcon)
    · by_contra hcon
      push Not at hcon
      exact h₂ ((oneRxn_hasMultistationarityCapacity_iff c d).mpr hcon)
  · rintro ⟨hcap, h₁, h₂⟩
    refine ⟨hcap, ?_, ?_⟩
    · intro h
      have hA : 1 < ∑ s ∈ univ.filter (fun s => a s < b s), a s :=
        (oneRxn_hasMultistationarityCapacity_iff a b).mp h
      exact (Nat.not_le.mpr hA) h₁
    · intro h
      have hA : 1 < ∑ s ∈ univ.filter (fun s => c s < d s), c s :=
        (oneRxn_hasMultistationarityCapacity_iff c d).mp h
      exact (Nat.not_le.mpr hA) h₂

/-- **A two-reaction atom has monostationary one-reaction subnetwork extensions.** If the
fully open two-reaction network is an atom of multistationarity, then each of its one-reaction
subnetwork extensions is *monostationary*: it has at most one positive steady state for every
choice of rate constants. -/
theorem twoRxnOpen_atom_monostationary (a b c d : Complex S) (h : TwoRxnIsAtom a b c d) :
    (∑ s ∈ univ.filter (fun s => a s < b s), a s) ≤ 1 ∧
      (∑ s ∈ univ.filter (fun s => c s < d s), c s) ≤ 1 :=
  (twoRxnOpen_isAtom_iff a b c d).mp h |>.2

/-! ### The reversible pair: the two reactions are each other's reverse -/

/-- The two-reaction network `a → b`, `b → a` is the reversible pair `a ⇌ b`. -/
theorem twoRxnOpen_revPair (a b : Complex S) : twoRxnOpen a b b a = revPair a b := rfl

/-- **The reversible pair.** The fully open extension of the two-reaction network
`a → b`, `b → a` is multistationary iff `∑_{i : b_i > a_i} a_i > 1` or
`∑_{i : a_i > b_i} b_i > 1` (Joshi 2013, Theorem 4.1(2), in the two-reaction form). -/
theorem twoRxnOpen_revPair_multistationary_iff (a b : Complex S) :
    (twoRxnOpen a b b a).fullyOpen.HasMultistationarityCapacity ↔
      1 < ∑ s ∈ univ.filter (fun s => a s < b s), a s ∨
        1 < ∑ s ∈ univ.filter (fun s => b s < a s), b s := by
  rw [twoRxnOpen_revPair, fullyOpen_hasMultistationarityCapacity_iff (revPair a b),
    revPair_multistationary_iff]

/-- **A reversible pair is never an atom of multistationarity.** If the two reactions are each
other's reverse, then whenever the pair is multistationary one of the two single reactions is
multistationary as well, so the pair is not minimal. -/
theorem twoRxnOpen_revPair_not_atom (a b : Complex S) : ¬ TwoRxnIsAtom a b b a := by
  rintro ⟨hcap, h₁, h₂⟩
  rcases (twoRxnOpen_revPair_multistationary_iff a b).mp hcap with h | h
  · exact h₁ ((oneRxn_hasMultistationarityCapacity_iff a b).mpr h)
  · exact h₂ ((oneRxn_hasMultistationarityCapacity_iff b a).mpr h)

/-! ### The shape of the two reaction vectors -/

/-- The reaction vector of the reaction `a → b`. -/
def rxnVec (a b : Complex S) : S → ℝ := fun s => (b s : ℝ) - a s

/-- Two reaction vectors **cross** if the first is positive where the second is negative and the
second is positive where the first is negative. -/
def Crosses (w₁ w₂ : S → ℝ) : Prop :=
  (∃ i, 0 < w₁ i ∧ w₂ i < 0) ∧ (∃ j, 0 < w₂ j ∧ w₁ j < 0)

/-- Two reaction vectors are **independent** if they are neither positive multiples nor
opposites of one another; equivalently, the two reactions are neither parallel nor a reversible
pair. -/
def VectorsIndependent (w₁ w₂ : S → ℝ) : Prop :=
  (∀ lam : ℝ, 0 < lam → (∀ s, w₂ s = lam * w₁ s) → False) ∧
    (∀ lam : ℝ, 0 < lam → (∀ s, w₂ s = -lam * w₁ s) → False)

/-- The two reactions `a → b` and `c → d` are **parallel** if their reaction vectors are
positive multiples of one another. -/
def ReactionsParallel (a b c d : Complex S) : Prop :=
  ∃ lam : ℝ, 0 < lam ∧ ∀ s, rxnVec c d s = lam * rxnVec a b s

omit [DecidableEq S] [Fintype S] in
/-- **Crossing reaction vectors are not parallel.** -/
theorem crossing_not_parallel {w₁ w₂ : S → ℝ} (h : Crosses w₁ w₂) :
    ¬ ∃ lam : ℝ, 0 < lam ∧ ∀ s, w₂ s = lam * w₁ s := by
  rintro ⟨lam, hlam, hmul⟩
  obtain ⟨i, hi₁, hi₂⟩ := h.1
  have hpos : 0 < lam * w₁ i := mul_pos hlam hi₁
  have : w₂ i = lam * w₁ i := hmul i
  linarith

omit [DecidableEq S] [Fintype S] in
/-- **A reversible pair has opposite reaction vectors.** -/
theorem revPair_vectors_opposite (a b : Complex S) (s : S) :
    rxnVec b a s = -(rxnVec a b s) := by
  simp only [rxnVec]; ring

omit [DecidableEq S] [Fintype S] in
/-- **A reversible pair is never independent.** -/
theorem revPair_not_independent (a b : Complex S) :
    ¬ VectorsIndependent (rxnVec a b) (rxnVec b a) := by
  rintro ⟨h₁, h₂⟩
  exact h₂ 1 one_pos (fun s => by simpa using revPair_vectors_opposite a b s)

omit [DecidableEq S] [Fintype S] in
/-- **A reversible pair crosses iff the two complexes are incomparable coordinatewise.**  The
reaction vectors of `a ⇌ b` are opposite, so they cross exactly when `a` is smaller than `b` in
one coordinate and larger in another. -/
theorem revPair_crosses_iff (a b : Complex S) :
    Crosses (rxnVec a b) (rxnVec b a) ↔ (∃ i, a i < b i) ∧ ∃ j, b j < a j := by
  constructor
  · rintro ⟨⟨i, h₁, h₂⟩, ⟨j, h₃, h₄⟩⟩
    have h₁' : (a i : ℝ) < b i := by
      simp only [rxnVec] at h₁
      linarith
    have h₃' : (b j : ℝ) < a j := by
      simp only [rxnVec] at h₃
      linarith
    exact ⟨⟨i, by exact_mod_cast h₁'⟩, ⟨j, by exact_mod_cast h₃'⟩⟩
  · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    have h₁' : (a i : ℝ) < b i := by exact_mod_cast hi
    have h₂' : (b j : ℝ) < a j := by exact_mod_cast hj
    refine ⟨⟨i, ?_, ?_⟩, ⟨j, ?_, ?_⟩⟩
    · simp only [rxnVec]; linarith
    · simp only [rxnVec]; linarith
    · simp only [rxnVec]; linarith
    · simp only [rxnVec]; linarith

omit [DecidableEq S] [Fintype S] in
/-- **Independent reaction vectors.** If the reaction vectors of `a → b` and `c → d` are
independent, then the two reactions are neither a reversible pair (`c = b`, `d = a`) nor
parallel (their vectors are not positive multiples of one another). -/
theorem independent_reactions (a b c d : Complex S)
    (h : VectorsIndependent (rxnVec a b) (rxnVec c d)) :
    ¬ (c = b ∧ d = a) ∧ ¬ ReactionsParallel a b c d := by
  constructor
  · intro hcon
    have hc : c = b := hcon.1
    have hd : d = a := hcon.2
    have hopp : ∀ s, rxnVec c d s = -(rxnVec a b s) := by
      intro s
      rw [hc, hd]
      exact revPair_vectors_opposite a b s
    exact h.2 1 one_pos (fun s => by simpa using hopp s)
  · rintro ⟨lam, hlam, hmul⟩
    exact h.1 lam hlam hmul

omit [DecidableEq S] [Fintype S] in
/-- **Parallel reactions are not independent.** -/
theorem parallel_not_independent (a b c d : Complex S) (h : ReactionsParallel a b c d) :
    ¬ VectorsIndependent (rxnVec a b) (rxnVec c d) := by
  obtain ⟨lam, hlam, hmul⟩ := h
  exact fun h' => h'.1 lam hlam hmul

/-! ### A concrete atom of multistationarity with crossing reaction vectors -/

namespace TwoReactionAtomExample

/-- The two species `X` (`false`) and `Y` (`true`). -/
abbrev Sp := Bool

/-- The complex `X + Y`. -/
def xy : Complex Sp := fun _ => 1

/-- The complex `3X`. -/
def threeX : Complex Sp := fun s => if s then 0 else 3

/-- The complex `2X + Y`. -/
def twoXY : Complex Sp := fun s => if s then 1 else 2

/-- The complex `X + 2Y`. -/
def xTwoY : Complex Sp := fun s => if s then 2 else 1

/-- The two-reaction network `X + Y → 3X`, `2X + Y → X + 2Y`, whose reaction vectors are
`(2, −1)` and `(−1, 1)`: they cross, and they are not proportional. -/
abbrev atomNet : Network Sp := twoRxnOpen xy threeX twoXY xTwoY

/-- **Rate constants for the atom.** The two non-flow reactions get the rates `39` and `54`,
the inflows the rates `2` (for `X`) and `11` (for `Y`), and the outflows the rate `26`.  (These
are the rates `3/2`, `27/13`, `1/13`, `11/26`, `1` multiplied by `26`; the mass-action field is
homogeneous of degree one in the rates, so the steady states are unchanged.) -/
def atomRates : atomNet.fullyOpen.RateConstants where
  k := fun r => Sum.elim
    (fun i : Fin 2 => if i = 0 then (39 : ℝ) else 54)
    (fun p : Bool ⊕ Bool => (Sum.elim (fun s : Bool => if s then 11 else 2)
      (fun _ : Bool => (26 : ℝ))) p) r
  positive := by
    intro r
    match r with
    | Sum.inl i =>
        show 0 < (if i = 0 then (39 : ℝ) else 54)
        by_cases hi : i = 0 <;> simp [hi]
    | Sum.inr (Sum.inl s) =>
        show 0 < (if s then 11 else 2)
        by_cases hs : s = true <;> simp [hs]
    | Sum.inr (Sum.inr s) =>
        show 0 < (26 : ℝ)
        norm_num

/-- The all-ones state is a steady state of the atom network. -/
theorem atom_steadyState_one :
    atomNet.fullyOpen.IsMassActionSteadyState atomRates (fun _ => (1 : ℝ)) := by
  intro s
  rw [twoRxnOpen_fullyOpen_field]
  cases s <;>
    simp [atomRates, Complex.massActionMonomial, xy, threeX, twoXY, xTwoY] <;> norm_num

/-- The all-thirds state is a second steady state of the atom network. -/
theorem atom_steadyState_third :
    atomNet.fullyOpen.IsMassActionSteadyState atomRates (fun _ => (1 / 3 : ℝ)) := by
  intro s
  rw [twoRxnOpen_fullyOpen_field]
  cases s <;>
    simp [atomRates, Complex.massActionMonomial, xy, threeX, twoXY, xTwoY] <;> norm_num

/-- **The two-reaction network `X + Y → 3X`, `2X + Y → X + 2Y` is multistationary.** -/
theorem atom_multistationary : atomNet.fullyOpen.HasMultistationarityCapacity := by
  refine (fullyOpen_hasMultistationarityCapacity_iff atomNet).mpr
    ⟨atomRates, fun _ => 1, fun _ => 1 / 3, ?_, ?_, ?_, ?_, ?_⟩
  · intro s; norm_num
  · intro s; norm_num
  · intro h
    have := congrFun h false
    norm_num at this
  · exact atom_steadyState_one
  · exact atom_steadyState_third

/-- The first reaction `X + Y → 3X` is *weak*: `∑_{i : b_i > a_i} a_i = 1 ≤ 1`. -/
theorem atom_sum_one : (∑ s ∈ univ.filter (fun s => xy s < threeX s), xy s) ≤ 1 := by
  decide

/-- The second reaction `2X + Y → X + 2Y` is *weak*: `∑_{i : d_i > c_i} c_i = 1 ≤ 1`. -/
theorem atom_sum_two : (∑ s ∈ univ.filter (fun s => twoXY s < xTwoY s), twoXY s) ≤ 1 := by
  decide

/-- **The network `X + Y → 3X`, `2X + Y → X + 2Y` is an atom of multistationarity.** -/
theorem atom_isAtom : TwoRxnIsAtom xy threeX twoXY xTwoY := by
  rw [twoRxnOpen_isAtom_iff]
  exact ⟨atom_multistationary, atom_sum_one, atom_sum_two⟩

/-- The reaction vectors of the atom network **cross**. -/
theorem atom_crosses : Crosses (rxnVec xy threeX) (rxnVec twoXY xTwoY) := by
  refine ⟨⟨false, ?_, ?_⟩, ⟨true, ?_, ?_⟩⟩
  · norm_num [rxnVec, xy, threeX]
  · norm_num [rxnVec, twoXY, xTwoY]
  · norm_num [rxnVec, twoXY, xTwoY]
  · norm_num [rxnVec, xy, threeX]

/-- The reaction vectors of the atom network are **independent**. -/
theorem atom_independent : VectorsIndependent (rxnVec xy threeX) (rxnVec twoXY xTwoY) := by
  constructor
  · rintro lam hlam hmul
    have h1 := hmul false
    have h2 := hmul true
    simp [rxnVec, xy, threeX, twoXY, xTwoY] at h1 h2
    linarith
  · rintro lam hlam hmul
    have h1 := hmul false
    have h2 := hmul true
    simp [rxnVec, xy, threeX, twoXY, xTwoY] at h1 h2
    linarith

end TwoReactionAtomExample

/-! ### A crossing pair that is never multistationary -/

namespace TwoReactionAtomExample

/-- The complex `X + Y`. -/
def srcXY : Complex Sp := fun _ => 1

/-- The complex `2X`. -/
def tgt2X : Complex Sp := fun s => if s then 0 else 2

/-- The complex `2Y`. -/
def tgt2Y : Complex Sp := fun s => if s then 2 else 0

/-- The two-reaction network `X + Y → 2X`, `X + Y → 2Y`.  Its reaction vectors are `(1, −1)`
and `(−1, 1)`, which cross. -/
abbrev crossNet : Network Sp := twoRxnOpen srcXY tgt2X srcXY tgt2Y

/-- **The vector field of the crossing network.** With `c = κ₀ − κ₁` the rate of the first
reaction minus the rate of the second, the field is
`c · (x_X x_Y) · (if s then −1 else 1) + inflow_s − outflow_s · x_s`. -/
theorem crossNet_field (κ : crossNet.fullyOpen.RateConstants) (p : Concentration Sp) (s : Bool) :
    crossNet.fullyOpen.massActionVectorField κ p s =
      (κ.k (Sum.inl (0 : Fin 2)) - κ.k (Sum.inl (1 : Fin 2))) * (p false * p true) *
          (if s then (-1 : ℝ) else 1) +
        κ.k (Sum.inr (Sum.inl s)) - κ.k (Sum.inr (Sum.inr s)) * p s := by
  rw [twoRxnOpen_fullyOpen_field]
  cases s <;>
    simp [crossNet, srcXY, tgt2X, tgt2Y, Complex.massActionMonomial] <;> ring

/-- **The crossing network `X + Y → 2X`, `X + Y → 2Y` has at most one positive steady state
for every choice of rate constants.**  Indeed, at a steady state
`l_X x_X = k_X + c x_X x_Y` and `l_Y x_Y = k_Y − c x_X x_Y` with `c = κ₀ − κ₁`, so all steady
states lie on the line `l_X x_X + l_Y x_Y = k_X + k_Y`; the first equation determines `x_X` as a
function of `x_Y` and the second determines `x_Y` as a function of `x_X`, and the two functions
are monotone in opposite directions, so at most one solution exists. -/
theorem crossNet_unique_of_lt (κ : crossNet.fullyOpen.RateConstants) {u v : Concentration Sp}
    (hu : u.Positive) (hv : v.Positive)
    (hus : crossNet.fullyOpen.IsMassActionSteadyState κ u)
    (hvs : crossNet.fullyOpen.IsMassActionSteadyState κ v)
    (hlt : u false < v false) : u = v := by
  set c : ℝ := κ.k (Sum.inl (0 : Fin 2)) - κ.k (Sum.inl (1 : Fin 2))
  set kX : ℝ := κ.k (Sum.inr (Sum.inl false))
  set kY : ℝ := κ.k (Sum.inr (Sum.inl true))
  set lX : ℝ := κ.k (Sum.inr (Sum.inr false))
  set lY : ℝ := κ.k (Sum.inr (Sum.inr true))
  have e1 : ∀ w : Concentration Sp, crossNet.fullyOpen.IsMassActionSteadyState κ w →
      lX * w false = kX + c * (w false * w true) := by
    intro w hw
    have h := hw false
    rw [crossNet_field] at h
    simp at h
    linarith
  have e2 : ∀ w : Concentration Sp, crossNet.fullyOpen.IsMassActionSteadyState κ w →
      lY * w true = kY - c * (w false * w true) := by
    intro w hw
    have h := hw true
    rw [crossNet_field] at h
    simp at h
    linarith
  have hkX0 : 0 < kX := by
    have : 0 < κ.k (Sum.inr (Sum.inl false)) := κ.positive _
    simpa [kX] using this
  have hkY0 : 0 < kY := by
    have : 0 < κ.k (Sum.inr (Sum.inl true)) := κ.positive _
    simpa [kY] using this
  have hlX0 : 0 < lX := by
    have : 0 < κ.k (Sum.inr (Sum.inr false)) := κ.positive _
    simpa [lX] using this
  have hlY0 : 0 < lY := by
    have : 0 < κ.k (Sum.inr (Sum.inr true)) := κ.positive _
    simpa [lY] using this
  -- all steady states lie on the same line `l_X x_X + l_Y x_Y = k_X + k_Y`
  have hline : lX * u false + lY * u true = lX * v false + lY * v true := by
    have h1 := e1 u hus
    have h2 := e2 u hus
    have h3 := e1 v hvs
    have h4 := e2 v hvs
    linarith
  -- hence `u true > v true`
  have hvt : v true < u true := by
    have h := hline
    have h' : lY * (u true - v true) = lX * (v false - u false) := by linarith
    have h'' : 0 < lY * (u true - v true) := by
      have : 0 < lX * (v false - u false) := by nlinarith
      linarith
    exact sub_pos.mp (pos_of_mul_pos_right h'' hlY0.le)
  by_cases hcpos : 0 < c
  · -- `c > 0`: `x_X` is increasing in `x_Y`
    have h1 : u false * (lX - c * u true) = kX := by nlinarith [e1 u hus]
    have h2 : v false * (lX - c * v true) = kX := by nlinarith [e1 v hvs]
    have h1pos : 0 < u false * (lX - c * u true) := by rw [h1]; exact hkX0
    have h2pos : 0 < v false * (lX - c * v true) := by rw [h2]; exact hkX0
    have hd1 : 0 < lX - c * u true := pos_of_mul_pos_right h1pos (hu false).le
    have hd2 : 0 < lX - c * v true := pos_of_mul_pos_right h2pos (hv false).le
    have hfac : lX - c * u true < lX - c * v true := by nlinarith
    have hs1 : u false * (lX - c * u true) < v false * (lX - c * u true) :=
      mul_lt_mul_of_pos_right hlt hd1
    have hs2 : v false * (lX - c * u true) < v false * (lX - c * v true) :=
      mul_lt_mul_of_pos_left hfac (hv false)
    nlinarith
  · -- `c ≤ 0`
    rcases lt_or_eq_of_le (le_of_not_gt hcpos) with hneg | hcz
    · -- `c < 0`: `x_Y` is increasing in `x_X`
      have h1 : u true * (lY + c * u false) = kY := by nlinarith [e2 u hus]
      have h2 : v true * (lY + c * v false) = kY := by nlinarith [e2 v hvs]
      have h1pos : 0 < u true * (lY + c * u false) := by rw [h1]; exact hkY0
      have h2pos : 0 < v true * (lY + c * v false) := by rw [h2]; exact hkY0
      have hd1 : 0 < lY + c * u false := pos_of_mul_pos_right h1pos (hu true).le
      have hd2 : 0 < lY + c * v false := pos_of_mul_pos_right h2pos (hv true).le
      have hfac : lY + c * v false < lY + c * u false := by nlinarith
      have hs1 : v true * (lY + c * u false) < u true * (lY + c * u false) :=
        mul_lt_mul_of_pos_right hvt hd1
      have hs2 : v true * (lY + c * v false) < v true * (lY + c * u false) :=
        mul_lt_mul_of_pos_left hfac (hv true)
      nlinarith
    · -- `c = 0`: the two equations are independent
      have h1 : lX * u false = kX := by
        have h := e1 u hus
        rw [hcz] at h
        linarith
      have h2 : lX * v false = kX := by
        have h := e1 v hvs
        rw [hcz] at h
        linarith
      have hmv : lX * u false < lX * v false := mul_lt_mul_of_pos_left hlt hlX0
      linarith

/-- The two steady states of the crossing network lie on the same line. -/
theorem crossNet_line (κ : crossNet.fullyOpen.RateConstants) {p q : Concentration Sp}
    (hsp : crossNet.fullyOpen.IsMassActionSteadyState κ p)
    (hsq : crossNet.fullyOpen.IsMassActionSteadyState κ q) :
    κ.k (Sum.inr (Sum.inr false)) * p false + κ.k (Sum.inr (Sum.inr true)) * p true =
      κ.k (Sum.inr (Sum.inr false)) * q false + κ.k (Sum.inr (Sum.inr true)) * q true := by
  have e1 : ∀ w : Concentration Sp, crossNet.fullyOpen.IsMassActionSteadyState κ w →
      κ.k (Sum.inr (Sum.inr false)) * w false = κ.k (Sum.inr (Sum.inl false)) +
        (κ.k (Sum.inl (0 : Fin 2)) - κ.k (Sum.inl (1 : Fin 2))) * (w false * w true) := by
    intro w hw
    have h := hw false
    rw [crossNet_field] at h
    simp at h
    linarith
  have e2 : ∀ w : Concentration Sp, crossNet.fullyOpen.IsMassActionSteadyState κ w →
      κ.k (Sum.inr (Sum.inr true)) * w true = κ.k (Sum.inr (Sum.inl true)) -
        (κ.k (Sum.inl (0 : Fin 2)) - κ.k (Sum.inl (1 : Fin 2))) * (w false * w true) := by
    intro w hw
    have h := hw true
    rw [crossNet_field] at h
    simp at h
    linarith
  have h1 := e1 p hsp
  have h2 := e2 p hsp
  have h3 := e1 q hsq
  have h4 := e2 q hsq
  linarith

/-- **The crossing network `X + Y → 2X`, `X + Y → 2Y` has at most one positive steady state
for every choice of rate constants.** -/
theorem crossNet_unique_steadyState (κ : crossNet.fullyOpen.RateConstants) {p q : Concentration Sp}
    (hp : p.Positive) (hq : q.Positive)
    (hsp : crossNet.fullyOpen.IsMassActionSteadyState κ p)
    (hsq : crossNet.fullyOpen.IsMassActionSteadyState κ q) : p = q := by
  by_cases hxy : p false = q false
  · have hyt : p true = q true := by
      have h := crossNet_line κ hsp hsq
      simp only [hxy] at h
      have h2 : κ.k (Sum.inr (Sum.inr true)) * p true = κ.k (Sum.inr (Sum.inr true)) * q true := by
        linarith
      exact mul_left_cancel₀ (κ.positive _).ne' h2
    funext s
    cases s <;> simp [hxy, hyt]
  · rcases lt_or_gt_of_ne hxy with hlt | hgt
    · exact crossNet_unique_of_lt κ hp hq hsp hsq hlt
    · exact (crossNet_unique_of_lt κ hq hp hsq hsp hgt).symm

/-- **The crossing network `X + Y → 2X`, `X + Y → 2Y` is never multistationary.** -/
theorem crossNet_not_multistationary : ¬ crossNet.fullyOpen.HasMultistationarityCapacity := by
  rintro ⟨κ, x₀, x, z, hx, hz, hsx, hsz, hne⟩
  exact hne (crossNet_unique_steadyState κ hx.2 hz.2 hsx hsz)

/-- The reaction vectors of the crossing network **cross**. -/
theorem crossNet_crosses : Crosses (rxnVec srcXY tgt2X) (rxnVec srcXY tgt2Y) := by
  refine ⟨⟨false, ?_, ?_⟩, ⟨true, ?_, ?_⟩⟩
  · norm_num [rxnVec, srcXY, tgt2X]
  · norm_num [rxnVec, srcXY, tgt2Y]
  · norm_num [rxnVec, srcXY, tgt2Y]
  · norm_num [rxnVec, srcXY, tgt2X]

end TwoReactionAtomExample

/-! ### A multistationary pair whose reaction vectors do not cross -/

namespace TwoReactionAtomExample

/-- The complex `X`. -/
def oneX : Complex Sp := fun s => if s then 0 else 1

/-- The complex `2X`. -/
def twoX : Complex Sp := fun s => if s then 0 else 2

/-- The complex `2Y`. -/
def twoY : Complex Sp := fun s => if s then 2 else 0

/-- The complex `3Y`. -/
def threeY : Complex Sp := fun s => if s then 3 else 0

/-- The two-reaction network `X → 2X`, `2Y → 3Y`.  Its reaction vectors are `(1, 0)` and
`(0, 1)`: they do **not** cross. -/
abbrev parallelNet : Network Sp := twoRxnOpen oneX twoX twoY threeY

/-- **Rate constants for the multistationary non-crossing pair:** the two non-flow reactions get
the rates `2` and `1`, the inflows the rate `2` (for both species) and the outflows the rates
`4` (for `X`) and `3` (for `Y`). -/
def parallelRates : parallelNet.fullyOpen.RateConstants where
  k := fun r => Sum.elim
    (fun i : Fin 2 => if i = 0 then (2 : ℝ) else 1)
    (fun p : Bool ⊕ Bool => (Sum.elim (fun _ : Bool => 2)
      (fun s : Bool => if s then 3 else 4)) p) r
  positive := by
    intro r
    match r with
    | Sum.inl i =>
        show 0 < (if i = 0 then (2 : ℝ) else 1)
        by_cases hi : i = 0 <;> simp [hi]
    | Sum.inr (Sum.inl s) =>
        show 0 < (2 : ℝ)
        norm_num
    | Sum.inr (Sum.inr s) =>
        show 0 < (if s then 3 else 4)
        by_cases hs : s = true <;> simp [hs]

/-- The state `(1, 1)` is a steady state of the non-crossing network. -/
theorem parallel_steadyState_one :
    parallelNet.fullyOpen.IsMassActionSteadyState parallelRates (fun _ => (1 : ℝ)) := by
  intro s
  rw [twoRxnOpen_fullyOpen_field]
  cases s <;>
    simp [parallelRates, Complex.massActionMonomial, oneX, twoX, twoY, threeY]
  all_goals norm_num

/-- The state `(1, 2)` is a second steady state of the non-crossing network. -/
theorem parallel_steadyState_two :
    parallelNet.fullyOpen.IsMassActionSteadyState parallelRates
      (fun s => if s then 2 else 1) := by
  intro s
  rw [twoRxnOpen_fullyOpen_field]
  cases s <;>
    simp [parallelRates, Complex.massActionMonomial, oneX, twoX, twoY, threeY]
  all_goals norm_num

/-- **The two-reaction network `X → 2X`, `2Y → 3Y` is multistationary**, even though its
reaction vectors do not cross: the second reaction alone (`2Y → 3Y`) is already multistationary
in the fully open network, since `∑_{i : b_i > a_i} a_i = 2 > 1`. -/
theorem parallel_multistationary : parallelNet.fullyOpen.HasMultistationarityCapacity := by
  refine (fullyOpen_hasMultistationarityCapacity_iff parallelNet).mpr
    ⟨parallelRates, fun _ => 1, fun s => if s then 2 else 1, ?_, ?_, ?_, ?_, ?_⟩
  · intro s; norm_num
  · intro s; cases s <;> norm_num
  · intro h
    have := congrFun h true
    norm_num at this
  · exact parallel_steadyState_one
  · exact parallel_steadyState_two

/-- The reaction vectors of the non-crossing network do **not** cross. -/
theorem parallel_not_crosses : ¬ Crosses (rxnVec oneX twoX) (rxnVec twoY threeY) := by
  rintro ⟨⟨i, h1, h2⟩, j⟩
  cases i with
  | false => norm_num [rxnVec, oneX, twoX, twoY, threeY] at h1 h2
  | true => norm_num [rxnVec, oneX, twoX, twoY, threeY] at h1

/-- The single reaction `2Y → 3Y` is multistationary in the fully open network, so the
non-crossing pair is **not** an atom of multistationarity. -/
theorem parallel_not_atom : ¬ TwoRxnIsAtom oneX twoX twoY threeY := by
  intro h
  obtain ⟨hcap, h1, h2⟩ := h
  exact h2 ((oneRxn_hasMultistationarityCapacity_iff twoY threeY).mpr (by decide))

end TwoReactionAtomExample

end Network

end CRNT
