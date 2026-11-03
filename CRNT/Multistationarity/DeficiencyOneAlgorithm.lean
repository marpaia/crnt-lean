import CRNT.Multistationarity.CapacityCharacterization
import CRNT.Multistationarity.OneReactionExistence
import CRNT.Deficiency.Signature
import CRNT.Open.Augmentation
import CRNT.Deficiency.Definition
import Mathlib.Basic.Sign.Basic

/-!
# Flux feasibility and multistationarity capacity

Feinberg's Deficiency One Algorithm (1995b) decides the capacity of a deficiency-one mass-action
network for multiple positive steady states by a **parameter-independent feasibility test**: one
solves, for the unknown log-ratio `μ = log y − log x` of the two candidate steady states, a finite
system of **linear inequalities** in `μ`, together with a **linear feasibility problem** in the
fluxes.  The algorithm affirms the capacity iff that system is feasible.

This module formalizes the semantic flux certificate `DOAFeasible` and proves that it exists
**iff** the network has the capacity for multiple steady states. Both directions hold for every
network, without a deficiency-one hypothesis. The certificate quantifies over real log-ratios
and fluxes and contains exponential balance equations. This existence characterization does not
provide the finite linear search of the published algorithm; the shelf/confluence and numerical
obligations are described below.

## The system

The unknown is the log-ratio `μ ∈ ℝ^𝒮` of the two candidate steady states.  The system asks for

* a **positive flux** `α ∈ ℝ^ᴿ` (the fluxes of the individual reactions at the lower state);
* the **flux balance at the lower state**, `∑_r α_r (y'_r − y_r) = 0`;
* the **flux balance at the upper state**, `∑_r α_r e^{⟨y_r, μ⟩} (y'_r − y_r) = 0`, the factor
  `e^{⟨y_r, μ⟩}` being the ratio of the reaction rates at the two states;
* the **sign compatibility** of `μ` with the stoichiometric subspace `S(N)`: `μ` must have the
  coordinatewise sign pattern of a nonzero stoichiometric vector, the sign pattern of `y − x`.

`DOACandidate` packages this data and `DOAFeasible` says that such a candidate exists.

## The correctness

* `doaFeasible_implies_capacity` — **the algorithmic direction**: a feasible system yields the
  capacity.  The witness is the flux certificate `(α, μ, σ)` of
  `CRNT.Network.hasMultistationarityCapacity_iff_flux_sign`, with `σ` the stoichiometric vector
  realizing the sign pattern of `μ`.
* `capacity_implies_doaFeasible` — **the converse direction**: a network with the capacity yields a
  feasible system; the log-ratio of the two witnessing steady states is the solution.
* `hasMultistationarityCapacity_iff_doaFeasible` — the two together: capacity is equivalent to
  the existence of a semantic flux certificate.
* `doa_feasible_implies_capacity` — the same statement in the classical deficiency-one setting
  (deficiency one, stoichiometric rank one, one-dimensional stoichiometric subspace), the shape in
  which Feinberg's theorem is usually stated.

## The rank-one case: the algorithm's linear inequality system

For a network whose stoichiometric subspace is a single line (`S(N) = span {v}`, `v ≠ 0`) the
algorithm's system collapses to a strikingly simple shape, which this module also formalizes:

* every reaction vector is `c_r • v` for a unique **reduced coefficient** `c_r`
  (`reducedCoefficient`), and the two flux balances become the **two scalar equations**
  `∑_r α_r c_r = 0` and `∑_r α_r e^{⟨y_r, μ⟩} c_r = 0`
  (`rankOne_lowerBalance_iff`, `rankOne_upperBalance_iff`);
* the pairing difference of a reaction is `c_r ⟨v, μ⟩` (`rankOne_pairingDifference`), so the
  algorithm's **linear inequality system** — the pairing order `⟨y'_r, μ⟩ ≷ ⟨y_r, μ⟩` prescribed
  by the sign of `c_r` — reduces to the **single linear inequality** `⟨v, μ⟩ ≠ 0`
  (`rankOne_pairingOrder_iff`), which in turn is implied by the sign compatibility
  (`rankOne_pairingOrder_of_sameSign`, via `classPairing_pos_of_sameSign`);
* consequently `RankOneDOASystem` is a single linear feasibility problem in `α`, and
  `rankOne_doaFeasible_iff` and `rankOne_hasMultistationarityCapacity_iff` are the algorithm's
  correctness in rank one.

## A family where the test is decided

`oneRxn_doaFeasible_iff` settles the algorithm on the fully open network with a single non-flow
reaction `a → b`: the test is feasible **iff** `∑_{b_i > a_i} a_i > 1` (Joshi 2013, Theorem 4.1),
so the algorithm is correct on that family.

## What is *not* formalized here

* The **shelf/confluence** presentation of the algorithm (`CRNT.Deficiency.DeficiencyOneAlgorithm`,
  `CRNT.Deficiency.Shelf`): the enumeration of shelf partitions and the confluence vectors that
  Feinberg's numerical version searches over, and the deduction of the linear inequality system
  from the network's combinatorial data.  The system formalized here is the *semantic* content of
  the algorithm — the conditions on `μ` and `α` whose feasibility the algorithm decides — and it
  is the correctness of that test which is proved.  In rank one, `RankOnePairingOrder` is the
  rank-one content of the shelf constraints: the pairing order prescribed by the sign of the
  reduced coefficient.
* The **numerical** version of the algorithm (Feinberg 1995b; Conradi–Feliu–Mincheva–Wiuf 2017):
  the reduction of the flux feasibility problem to a linear program over the sign patterns of the
  fluxes, and the decision procedure.
* The **Advanced Deficiency Algorithm** (leaf M8), whose verdict `CRNT.Network.ADAAffirmsCapacity`
  is a shelf partition over colinearity classes; its correctness is not proved here either.
-/

namespace CRNT
namespace Network

open scoped BigOperators
open Finset

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Two same-sign vectors have the same `SignType` sign at every coordinate. -/
theorem sameSign_sign_eq {ι : Type} {u v : ι → ℝ} (h : SameSign u v) (i : ι) :
    SignType.sign (u i) = SignType.sign (v i) := by
  rcases lt_trichotomy (u i) 0 with hu | hu | hu
  · rw [sign_neg hu, sign_neg ((h i).2.mp hu)]
  · have : v i = 0 := by
      rcases lt_trichotomy (v i) 0 with hv | hv | hv
      · exact absurd ((h i).2.mpr hv) (by rw [hu]; exact lt_irrefl 0)
      · exact hv
      · exact absurd ((h i).1.mpr hv) (by rw [hu]; exact lt_irrefl 0)
    rw [hu, this, sign_zero]
  · rw [sign_pos hu, sign_pos ((h i).1.mp hu)]

/-- Same sign patterns give same-sign vectors. -/
theorem sameSign_of_sign_eq {ι : Type} {u v : ι → ℝ}
    (h : ∀ i, SignType.sign (u i) = SignType.sign (v i)) : SameSign u v := by
  intro i
  constructor
  · constructor
    · intro hu
      have h1 : SignType.sign (u i) = SignType.pos := sign_pos hu
      rw [h i] at h1
      exact sign_eq_one_iff.mp h1
    · intro hu
      have h1 : SignType.sign (v i) = SignType.pos := sign_pos hu
      rw [← h i] at h1
      exact sign_eq_one_iff.mp h1
  · constructor
    · intro hu
      have h1 : SignType.sign (u i) = SignType.neg := sign_neg hu
      rw [h i] at h1
      exact sign_eq_neg_one_iff.mp h1
    · intro hu
      have h1 : SignType.sign (v i) = SignType.neg := sign_neg hu
      rw [← h i] at h1
      exact sign_eq_neg_one_iff.mp h1

/-- **Sign compatibility with the stoichiometric subspace, in sign-vector form.** A log-ratio is
sign-compatible with `S(N)` iff some nonzero stoichiometric vector has the same `SignType` sign
pattern — the pattern of `y − x`. -/
theorem signCompatibleWithStoich_iff (N : Network S) (μ : S → ℝ) (hμ0 : μ ≠ 0) :
    N.SignCompatibleWithStoich μ ↔
      ∃ σ ∈ N.stoichSubspace, σ ≠ 0 ∧ (∀ s, SignType.sign (σ s) = SignType.sign (μ s)) := by
  constructor
  · rintro ⟨σ, hσ, hsame⟩
    refine ⟨σ, hσ, ?_, fun s => sameSign_sign_eq hsame s⟩
    intro hσ0
    obtain ⟨s, hs⟩ := Function.ne_iff.mp hμ0
    simp only [Pi.zero_apply] at hs
    have hσs : σ s = 0 := by rw [hσ0]; simp
    rcases lt_or_gt_of_ne hs with hlt | hgt
    · exact absurd ((hsame s).2.mpr hlt) (by rw [hσs]; exact lt_irrefl 0)
    · exact absurd ((hsame s).1.mpr hgt) (by rw [hσs]; exact lt_irrefl 0)
  · rintro ⟨σ, hσ, hσ0, hsign⟩
    exact ⟨σ, hσ, sameSign_of_sign_eq hsign⟩

/-! ### The algorithm's system -/

/-- **A candidate solution of the Deficiency One Algorithm.** The data are the log-ratio `μ` of the
two candidate steady states, the positive flux `α` at the lower state, the two flux balances, and
the sign compatibility of `μ` with the stoichiometric subspace. -/
structure DOACandidate (N : Network S) where
  /-- The candidate log-ratio `μ = log y − log x`. -/
  μ : S → ℝ
  /-- The candidate flux at the lower state. -/
  α : N.R → ℝ
  /-- The log-ratio is nonzero: the two candidate steady states differ. -/
  μ_ne_zero : μ ≠ 0
  /-- The flux is strictly positive. -/
  α_pos : ∀ r, 0 < α r
  /-- The log-ratio is sign-compatible with the stoichiometric subspace. -/
  sign_compatible : N.SignCompatibleWithStoich μ
  /-- The flux balance at the lower state, `∑_r α_r (y'_r − y_r) = 0`. -/
  lower_balance : ∀ s, ∑ r, α r * N.reactionVector r s = 0
  /-- The flux balance at the upper state, `∑_r α_r e^{⟨y_r, μ⟩} (y'_r − y_r) = 0`. -/
  upper_balance : ∀ s, ∑ r, α r * Real.exp (complexPairing (N.reaction r).source μ) *
    N.reactionVector r s = 0

/-- **The Deficiency One Algorithm's system is feasible**: there is a log-ratio `μ` and a positive
flux `α` meeting the flux balances and the sign compatibility.  This is the condition the
algorithm tests. -/
def DOAFeasible (N : Network S) : Prop := Nonempty (DOACandidate N)

/-! ### The correctness of the algorithm -/

/-- **The algorithmic direction of the Deficiency One Algorithm: a feasible system yields the
capacity for multiple steady states.**

The witness is the flux certificate `(α, μ, σ)` of
`CRNT.Network.hasMultistationarityCapacity_iff_flux_sign`: `σ` is the stoichiometric vector
realizing the sign pattern of `μ`, extracted from the sign compatibility.  The proof does not use
the deficiency-one hypothesis: the test is correct for every network. -/
theorem doaFeasible_implies_capacity (N : Network S) (h : N.DOAFeasible) :
    N.HasMultistationarityCapacity := by
  obtain ⟨d⟩ := h
  obtain ⟨σ, hσ, hσ0, hsign⟩ :=
    (N.signCompatibleWithStoich_iff d.μ d.μ_ne_zero).mp d.sign_compatible
  exact (N.hasMultistationarityCapacity_iff_flux_sign).2
    ⟨d.α, d.μ, σ, d.α_pos, hσ, hσ0, hsign, d.lower_balance, d.upper_balance⟩

/-- **The converse direction of the Deficiency One Algorithm: the capacity yields a feasible
system.**  The solution is the log-ratio of the two witnessing steady states, and the flux is
their flux at the lower one. -/
theorem capacity_implies_doaFeasible (N : Network S) (h : N.HasMultistationarityCapacity) :
    N.DOAFeasible := by
  obtain ⟨α, μ, σ, hα, hσS, hσ0, hsign, hflux, hflux'⟩ :=
    (N.hasMultistationarityCapacity_iff_flux_sign).1 h
  have hμ0 : μ ≠ 0 := by
    intro hμ0
    obtain ⟨s, hs⟩ := Function.ne_iff.mp hσ0
    have hs0 : σ s ≠ 0 := by simpa only [Pi.zero_apply] using hs
    have h1 : SignType.sign (μ s) = SignType.sign (σ s) := (hsign s).symm
    have h2 : SignType.sign (μ s) = 0 := by rw [hμ0, Pi.zero_apply, sign_zero]
    rw [h2] at h1
    have h3 : SignType.sign (σ s) = 0 := h1.symm
    rw [sign_eq_zero_iff] at h3
    exact hs0 h3
  have hsc : N.SignCompatibleWithStoich μ := ⟨σ, hσS, sameSign_of_sign_eq hsign⟩
  exact ⟨{ μ := μ, α := α, μ_ne_zero := hμ0, α_pos := hα, sign_compatible := hsc, lower_balance := hflux, upper_balance := hflux' }⟩

/-- Multistationarity capacity is equivalent to the existence of a semantic flux certificate.
This theorem does not supply a decision procedure for the real existential statement. -/
theorem hasMultistationarityCapacity_iff_doaFeasible (N : Network S) :
    N.HasMultistationarityCapacity ↔ N.DOAFeasible :=
  ⟨N.capacity_implies_doaFeasible, N.doaFeasible_implies_capacity⟩

/-! ### The rank-one case -/

/-- Every reaction vector of a rank-one network is a multiple of the class direction `v`. -/
theorem exists_reducedCoefficient (N : Network S) (v : S → ℝ)
    (hspan : N.stoichSubspace = Submodule.span ℝ {v}) (r : N.R) :
    ∃ c : ℝ, N.reactionVector r = c • v := by
  have hr : N.reactionVector r ∈ N.stoichSubspace := N.reactionVector_mem_stoichSubspace r
  rw [hspan] at hr
  obtain ⟨c, hc⟩ := (Submodule.mem_span_singleton).mp hr
  exact ⟨c, hc.symm⟩

/-- The reduced coefficient is unique. -/
theorem reducedCoefficient_unique (N : Network S) (v : S → ℝ) (hv : v ≠ 0) (r : N.R)
    (c₁ c₂ : ℝ) (h₁ : N.reactionVector r = c₁ • v) (h₂ : N.reactionVector r = c₂ • v) :
    c₁ = c₂ := by
  obtain ⟨s, hs⟩ := Function.ne_iff.mp hv
  have hs0 : v s ≠ 0 := by simpa only [Pi.zero_apply] using hs
  have h12 : c₁ • v = c₂ • v := by rw [← h₁, h₂]
  have hz : (c₁ - c₂) • v = 0 := by rw [sub_smul, h12, sub_self]
  have hz' : (c₁ - c₂) * v s = 0 := by
    have hcon := congrFun hz s
    simpa [Pi.smul_apply, smul_eq_mul] using hcon
  have hdiff : c₁ - c₂ = 0 := (mul_eq_zero.mp hz').resolve_right hs0
  exact sub_eq_zero.mp hdiff

/-- **The reduced coefficient of a reaction in a rank-one network**: the unique real `c` with
`N.reactionVector r = c • v`. -/
noncomputable def reducedCoefficient (N : Network S) (v : S → ℝ) (_hv : v ≠ 0)
    (hspan : N.stoichSubspace = Submodule.span ℝ {v}) (r : N.R) : ℝ :=
  Classical.choose (exists_reducedCoefficient N v hspan r)

/-- **The reduced coefficient realizes the reaction vector.** -/
theorem reducedCoefficient_spec (N : Network S) (v : S → ℝ) (hv : v ≠ 0)
    (hspan : N.stoichSubspace = Submodule.span ℝ {v}) (r : N.R) :
    N.reactionVector r = reducedCoefficient N v hv hspan r • v := by
  exact Classical.choose_spec (exists_reducedCoefficient N v hspan r)

/-- The reaction vector of `r`, at a coordinate, is the reduced coefficient times `v`. -/
theorem reducedCoefficient_apply (N : Network S) (v : S → ℝ) (hv : v ≠ 0)
    (hspan : N.stoichSubspace = Submodule.span ℝ {v}) (r : N.R) (s : S) :
    N.reactionVector r s = reducedCoefficient N v hv hspan r * v s := by
  have h := congrFun (reducedCoefficient_spec N v hv hspan r) s
  simpa [Pi.smul_apply, smul_eq_mul] using h

/-- A rank-one network has a nontrivial reaction: some reduced coefficient is nonzero. -/
theorem exists_reducedCoefficient_ne_zero (N : Network S) (v : S → ℝ) (hv : v ≠ 0)
    (hspan : N.stoichSubspace = Submodule.span ℝ {v}) :
    ∃ r : N.R, reducedCoefficient N v hv hspan r ≠ 0 := by
  by_contra hall
  push Not at hall
  have hz : ∀ r : N.R, N.reactionVector r = 0 := by
    intro r
    rw [reducedCoefficient_spec N v hv hspan r, hall r, zero_smul]
  have hle : N.stoichSubspace ≤ ⊥ := by
    rw [stoichSubspace]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨r, rfl⟩
    exact hz r
  have hbot : N.stoichSubspace = ⊥ := le_antisymm hle bot_le
  have hne : N.stoichSubspace ≠ ⊥ := by
    rw [hspan]
    exact (Submodule.ne_bot_iff _).mpr ⟨v, Submodule.mem_span_singleton_self v, hv⟩
  exact hne hbot

/-- **In a rank-one network the lower-state flux balance is a single scalar equation.** -/
theorem rankOne_lowerBalance_iff (N : Network S) (v : S → ℝ) (hv : v ≠ 0)
    (hspan : N.stoichSubspace = Submodule.span ℝ {v}) (α : N.R → ℝ) :
    (∀ s, ∑ r, α r * N.reactionVector r s = 0) ↔
      ∑ r, α r * reducedCoefficient N v hv hspan r = 0 := by
  constructor
  · intro h
    obtain ⟨s, hs⟩ := Function.ne_iff.mp hv
    have hs0 : v s ≠ 0 := by simpa only [Pi.zero_apply] using hs
    have h1 : (∑ r, α r * reducedCoefficient N v hv hspan r) * v s = 0 := by
      calc (∑ r, α r * reducedCoefficient N v hv hspan r) * v s
          = ∑ r, (α r * reducedCoefficient N v hv hspan r) * v s := by
              rw [Finset.sum_mul]
        _ = ∑ r, α r * N.reactionVector r s := by
            refine Finset.sum_congr rfl fun r _ => ?_
            rw [reducedCoefficient_apply N v hv hspan r s]
            ring
        _ = 0 := h s
    rw [mul_eq_zero] at h1
    exact h1.resolve_right hs0
  · intro h s
    calc ∑ r, α r * N.reactionVector r s
        = ∑ r, (α r * reducedCoefficient N v hv hspan r) * v s := by
            refine Finset.sum_congr rfl fun r _ => ?_
            rw [reducedCoefficient_apply N v hv hspan r s]
            ring
      _ = (∑ r, α r * reducedCoefficient N v hv hspan r) * v s := by rw [← Finset.sum_mul]
      _ = 0 := by rw [h, zero_mul]
      _ = 0 := by simp

/-- **In a rank-one network the upper-state flux balance is a single scalar equation.** -/
theorem rankOne_upperBalance_iff (N : Network S) (v : S → ℝ) (hv : v ≠ 0)
    (hspan : N.stoichSubspace = Submodule.span ℝ {v}) (α : N.R → ℝ) (μ : S → ℝ) :
    (∀ s, ∑ r, α r * Real.exp (complexPairing (N.reaction r).source μ) * N.reactionVector r s = 0) ↔
      ∑ r, α r * Real.exp (complexPairing (N.reaction r).source μ) *
        reducedCoefficient N v hv hspan r = 0 := by
  constructor
  · intro h
    obtain ⟨s, hs⟩ := Function.ne_iff.mp hv
    have hs0 : v s ≠ 0 := by simpa only [Pi.zero_apply] using hs
    have h1 : (∑ r, α r * Real.exp (complexPairing (N.reaction r).source μ) *
        reducedCoefficient N v hv hspan r) * v s = 0 := by
      calc (∑ r, α r * Real.exp (complexPairing (N.reaction r).source μ) *
            reducedCoefficient N v hv hspan r) * v s
          = ∑ r, (α r * Real.exp (complexPairing (N.reaction r).source μ) *
              reducedCoefficient N v hv hspan r) * v s := by rw [Finset.sum_mul]
        _ = ∑ r, α r * Real.exp (complexPairing (N.reaction r).source μ) * N.reactionVector r s := by
            refine Finset.sum_congr rfl fun r _ => ?_
            rw [reducedCoefficient_apply N v hv hspan r s]
            ring
        _ = 0 := h s
    rw [mul_eq_zero] at h1
    exact h1.resolve_right hs0
  · intro h s
    calc ∑ r, α r * Real.exp (complexPairing (N.reaction r).source μ) * N.reactionVector r s
        = ∑ r, (α r * Real.exp (complexPairing (N.reaction r).source μ) *
            reducedCoefficient N v hv hspan r) * v s := by
            refine Finset.sum_congr rfl fun r _ => ?_
            rw [reducedCoefficient_apply N v hv hspan r s]
            ring
      _ = (∑ r, α r * Real.exp (complexPairing (N.reaction r).source μ) *
            reducedCoefficient N v hv hspan r) * v s := by rw [← Finset.sum_mul]
      _ = 0 := by rw [h, zero_mul]
      _ = 0 := by simp

/-- **The pairing of the class direction with the log-ratio.** -/
def classPairing (v μ : S → ℝ) : ℝ := ∑ s, v s * μ s

/-- **The pairing difference of a reaction is its reduced coefficient times the class pairing.**
For a rank-one network, the difference of the pairings of the target and the source of `r` is
`c_r ⟨v, μ⟩`. -/
theorem rankOne_pairingDifference (N : Network S) (v : S → ℝ) (hv : v ≠ 0)
    (hspan : N.stoichSubspace = Submodule.span ℝ {v}) (r : N.R) (μ : S → ℝ) :
    complexPairing (N.reaction r).target μ - complexPairing (N.reaction r).source μ =
      reducedCoefficient N v hv hspan r * classPairing v μ := by
  have h1 : complexPairing (N.reaction r).target μ - complexPairing (N.reaction r).source μ =
      ∑ s, N.reactionVector r s * μ s := by
    simp only [complexPairing]
    have hsub : (∑ s : S, (((N.reaction r).target s : ℝ) * μ s)) -
        (∑ s : S, (((N.reaction r).source s : ℝ) * μ s)) =
        ∑ s : S, ((((N.reaction r).target s : ℝ) * μ s) - (((N.reaction r).source s : ℝ) * μ s)) := by
      exact (Finset.sum_sub_distrib (s := (Finset.univ : Finset S))
        (f := fun s : S => (((N.reaction r).target s : ℝ) * μ s))
        (g := fun s : S => (((N.reaction r).source s : ℝ) * μ s))).symm
    rw [hsub]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [reactionVector_apply]
    ring
  have h2 : ∑ s, N.reactionVector r s * μ s =
      ∑ s, (reducedCoefficient N v hv hspan r * v s) * μ s := by
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [reducedCoefficient_apply N v hv hspan r s]
  have h3 : ∑ s, (reducedCoefficient N v hv hspan r * v s) * μ s =
      reducedCoefficient N v hv hspan r * ∑ s, v s * μ s := by
    calc ∑ s, (reducedCoefficient N v hv hspan r * v s) * μ s
        = ∑ s, reducedCoefficient N v hv hspan r * (v s * μ s) := by
            refine Finset.sum_congr rfl fun s _ => ?_
            ring
      _ = reducedCoefficient N v hv hspan r * ∑ s, v s * μ s := by rw [Finset.mul_sum]
  rw [h1, h2, h3, classPairing]

/-- **The sign of the pairing difference of a reaction** at the log-ratio `μ`: the sign of
`⟨y'_r, μ⟩ − ⟨y_r, μ⟩`. -/
noncomputable def pairingDifferenceSign (N : Network S) (r : N.R) (μ : S → ℝ) : SignType :=
  SignType.sign (complexPairing (N.reaction r).target μ - complexPairing (N.reaction r).source μ)

/-- **The Deficiency One Algorithm's linear inequality system, in the rank-one reduced
coordinates.**  For each reaction, the pairing order of its source and its target is prescribed
by the sign of its reduced coefficient, up to a global orientation `η`.

By `rankOne_pairingDifference` the pairing difference of reaction `r` is `c_r ⟨v, μ⟩`, so the
condition on `r` is the **linear inequality** `c_r ⟨v, μ⟩ ≷ 0` with the direction prescribed by
`η` and by the sign of `c_r`; the orientation `η` is the direction of the class in which the
second state lies. -/
def RankOnePairingOrder (N : Network S) (v : S → ℝ) (hv : v ≠ 0)
    (hspan : N.stoichSubspace = Submodule.span ℝ {v}) (μ : S → ℝ) : Prop :=
  ∃ η : SignType, (η = 1 ∨ η = -1) ∧
    ∀ r : N.R, reducedCoefficient N v hv hspan r ≠ 0 →
      pairingDifferenceSign N r μ = η * SignType.sign (reducedCoefficient N v hv hspan r)

/-- **In a rank-one network the algorithm's linear inequality system is a single linear
inequality**: the pairing order system is feasible iff the class pairing `⟨v, μ⟩` is nonzero. -/
theorem rankOne_pairingOrder_iff (N : Network S) (v : S → ℝ) (hv : v ≠ 0)
    (hspan : N.stoichSubspace = Submodule.span ℝ {v}) (μ : S → ℝ) :
    N.RankOnePairingOrder v hv hspan μ ↔ classPairing v μ ≠ 0 := by
  have hex : ∃ r : N.R, reducedCoefficient N v hv hspan r ≠ 0 :=
    N.exists_reducedCoefficient_ne_zero v hv hspan
  have hdiff : ∀ r : N.R,
      pairingDifferenceSign N r μ =
        SignType.sign (reducedCoefficient N v hv hspan r) * SignType.sign (classPairing v μ) := by
    intro r
    have hd := rankOne_pairingDifference N v hv hspan r μ
    rw [pairingDifferenceSign, hd]
    exact sign_mul _ _
  constructor
  · rintro ⟨η, hη, h⟩
    obtain ⟨r, hr⟩ := hex
    intro hz
    exfalso
    have hsignP : SignType.sign (classPairing v μ) = 0 := by
      rw [sign_eq_zero_iff]
      exact hz
    have h1 := h r hr
    rw [hdiff r, hsignP] at h1
    rcases hη with hη | hη
    · rw [hη] at h1
      have hz' : SignType.sign (reducedCoefficient N v hv hspan r) = 0 := by
        simpa using h1.symm
      rw [sign_eq_zero_iff] at hz'
      exact hr hz'
    · rw [hη] at h1
      have hz' : SignType.sign (reducedCoefficient N v hv hspan r) = 0 := by
        rcases SignType.trichotomy (SignType.sign (reducedCoefficient N v hv hspan r)) with
          htr | htr | htr
        · rw [htr] at h1
          exact absurd h1 (by decide)
        · exact htr
        · rw [htr] at h1
          exact absurd h1 (by decide)
      rw [sign_eq_zero_iff] at hz'
      exact hr hz'
  · intro h
    refine ⟨SignType.sign (classPairing v μ), ?_, ?_⟩
    · rcases SignType.trichotomy (SignType.sign (classPairing v μ)) with htr | htr | htr
      · exact Or.inr htr
      · exact absurd htr (by rw [sign_eq_zero_iff]; exact h)
      · exact Or.inl htr
    · intro r hr
      calc pairingDifferenceSign N r μ
          = SignType.sign (reducedCoefficient N v hv hspan r) * SignType.sign (classPairing v μ) :=
            hdiff r
        _ = SignType.sign (classPairing v μ) * SignType.sign (reducedCoefficient N v hv hspan r) := by
            rw [mul_comm]

/-! ### The rank-one system: the algorithm reduces to one linear program -/

/-- **A positive multiple of a vector has the same sign pattern.** -/
theorem sameSign_smul_pos {ι : Type} {t : ℝ} (ht : 0 < t) {v μ : ι → ℝ} (h : SameSign (t • v) μ) :
    SameSign v μ := by
  intro s
  have hts : (t • v) s = t * v s := by simp [Pi.smul_apply, smul_eq_mul]
  constructor
  · constructor
    · intro hv
      have h1 : 0 < (t • v) s := by rw [hts]; exact mul_pos ht hv
      exact (h s).1.mp h1
    · intro hv
      have h1 : 0 < (t • v) s := (h s).1.mpr hv
      have h2 : 0 < t * v s := by rw [← hts]; exact h1
      rcases mul_pos_iff.mp h2 with h | h
      · exact h.2
      · exact absurd h.1 (by linarith)
  · constructor
    · intro hv
      have h1 : (t • v) s < 0 := by
        rw [hts, mul_comm]
        exact mul_neg_of_neg_of_pos hv ht
      exact (h s).2.mp h1
    · intro hv
      have h1 : (t • v) s < 0 := (h s).2.mpr hv
      have h2 : t * v s < 0 := by rw [← hts]; exact h1
      rcases mul_neg_iff.mp h2 with h | h
      · exact h.2
      · exact absurd h.1 (by linarith)

/-- **A negative multiple of a vector has the sign pattern of its negation.** -/
theorem sameSign_smul_neg {ι : Type} {t : ℝ} (ht : t < 0) {v μ : ι → ℝ} (h : SameSign (t • v) μ) :
    SameSign (-v) μ := by
  have h1 : SameSign ((-t) • (-v)) μ := by
    intro s
    have heq : (t • v) s = ((-t) • (-v)) s := by
      simp only [Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
      ring
    constructor
    · constructor
      · intro ha
        rw [← heq] at ha
        exact (h s).1.mp ha
      · intro ha
        have h1 : 0 < (t • v) s := (h s).1.mpr ha
        rw [← heq]
        exact h1
    · constructor
      · intro ha
        rw [← heq] at ha
        exact (h s).2.mp ha
      · intro ha
        have h1 : (t • v) s < 0 := (h s).2.mpr ha
        rw [← heq]
        exact h1
  exact sameSign_smul_pos (neg_pos.mpr ht) h1

/-- **The Deficiency One Algorithm's system in the rank-one reduced coordinates.**  The log-ratio
`μ` has the sign pattern of the class direction (or of its opposite), the flux `α` is positive, and
the two flux balances are the two **scalar** equations `∑_r α_r c_r = 0` and
`∑_r α_r e^{⟨y_r, μ⟩} c_r = 0`. -/
def RankOneDOASystem (N : Network S) (v : S → ℝ) (hv : v ≠ 0)
    (hspan : N.stoichSubspace = Submodule.span ℝ {v}) : Prop :=
  ∃ (μ : S → ℝ) (α : N.R → ℝ),
    μ ≠ 0 ∧ (∀ r, 0 < α r) ∧ (SameSign μ v ∨ SameSign μ (-v)) ∧
    (∑ r, α r * reducedCoefficient N v hv hspan r = 0) ∧
    (∑ r, α r * Real.exp (complexPairing (N.reaction r).source μ) *
      reducedCoefficient N v hv hspan r = 0)

/-- **In a rank-one network the algorithm's system is the rank-one system.**  The two vector flux
balances are the two scalar balances, and the sign compatibility with `S(N) = span {v}` is the
requirement that `μ` have the sign pattern of the class direction or of its opposite. -/
theorem rankOne_doaFeasible_iff (N : Network S) (v : S → ℝ) (hv : v ≠ 0)
    (hspan : N.stoichSubspace = Submodule.span ℝ {v}) :
    N.DOAFeasible ↔ N.RankOneDOASystem v hv hspan := by
  constructor
  · rintro ⟨d⟩
    obtain ⟨w, hw, hsame⟩ := d.sign_compatible
    rw [hspan] at hw
    obtain ⟨t, ht⟩ := (Submodule.mem_span_singleton).mp hw
    have hw0 : w ≠ 0 := by
      intro hw0
      obtain ⟨s, hs⟩ := Function.ne_iff.mp d.μ_ne_zero
      have hs0 : d.μ s ≠ 0 := by
        intro hs0
        simp only [Pi.zero_apply] at hs
        exact hs hs0
      have hws : w s = 0 := by rw [hw0]; simp
      rcases lt_or_gt_of_ne hs0 with hneg | hpos
      · have := (hsame s).2.mpr hneg
        rw [hws] at this
        exact lt_irrefl 0 this
      · have := (hsame s).1.mpr hpos
        rw [hws] at this
        exact lt_irrefl 0 this
    have ht0 : t ≠ 0 := by
      intro ht0
      exact hw0 (by rw [← ht, ht0, zero_smul])
    refine ⟨d.μ, d.α, d.μ_ne_zero, d.α_pos, ?_, ?_, ?_⟩
    · rcases lt_or_gt_of_ne ht0 with htneg | htpos
      · exact Or.inr (sameSign_symm (sameSign_smul_neg htneg (by rw [ht]; exact hsame)))
      · exact Or.inl (sameSign_symm (sameSign_smul_pos htpos (by rw [ht]; exact hsame)))
    · exact (N.rankOne_lowerBalance_iff v hv hspan d.α).mp d.lower_balance
    · exact (N.rankOne_upperBalance_iff v hv hspan d.α d.μ).mp d.upper_balance
  · rintro ⟨μ, α, hμ0, hα, hsame, hlow, hupp⟩
    have hsc : N.SignCompatibleWithStoich μ := by
      rcases hsame with h | h
      · refine ⟨v, ?_, sameSign_symm h⟩
        rw [hspan]
        exact Submodule.mem_span_singleton_self v
      · refine ⟨-v, ?_, sameSign_symm h⟩
        have hmem : v ∈ Submodule.span ℝ ({v} : Set (S → ℝ)) := Submodule.mem_span_singleton_self v
        rw [hspan]
        exact Submodule.neg_mem (p := Submodule.span ℝ ({v} : Set (S → ℝ))) hmem
    have hlb : ∀ s, ∑ r, α r * N.reactionVector r s = 0 :=
      (N.rankOne_lowerBalance_iff v hv hspan α).mpr hlow
    have hub : ∀ s, ∑ r, α r * Real.exp (complexPairing (N.reaction r).source μ) *
        N.reactionVector r s = 0 :=
      (N.rankOne_upperBalance_iff v hv hspan α μ).mpr hupp
    exact ⟨{ μ := μ, α := α, μ_ne_zero := hμ0, α_pos := hα, sign_compatible := hsc, lower_balance := hlb, upper_balance := hub }⟩

/-- **The Deficiency One Algorithm is correct in rank one.**  A network whose stoichiometric
subspace is a line has the capacity for multiple steady states iff the algorithm's system — two
scalar flux balances and the sign compatibility of the log-ratio — is feasible. -/
theorem rankOne_hasMultistationarityCapacity_iff (N : Network S) (v : S → ℝ) (hv : v ≠ 0)
    (hspan : N.stoichSubspace = Submodule.span ℝ {v}) :
    N.HasMultistationarityCapacity ↔ N.RankOneDOASystem v hv hspan :=
  (N.hasMultistationarityCapacity_iff_doaFeasible).trans (N.rankOne_doaFeasible_iff v hv hspan)

/-- **The algorithmic direction in rank one.** -/
theorem rankOne_doaFeasible_implies_capacity (N : Network S) (v : S → ℝ) (hv : v ≠ 0)
    (hspan : N.stoichSubspace = Submodule.span ℝ {v}) (h : N.RankOneDOASystem v hv hspan) :
    N.HasMultistationarityCapacity :=
  N.doaFeasible_implies_capacity ((N.rankOne_doaFeasible_iff v hv hspan).mpr h)

/-- **The converse direction in rank one.** -/
theorem rankOne_capacity_implies_doaFeasible (N : Network S) (v : S → ℝ) (hv : v ≠ 0)
    (hspan : N.stoichSubspace = Submodule.span ℝ {v}) (h : N.HasMultistationarityCapacity) :
    N.RankOneDOASystem v hv hspan :=
  (N.rankOne_doaFeasible_iff v hv hspan).mp (N.capacity_implies_doaFeasible h)

/-- **Same-sign vectors vanish together.** -/
theorem sameSign_zero_iff {ι : Type} {u v : ι → ℝ} (h : SameSign u v) (s : ι) :
    u s = 0 ↔ v s = 0 := by
  constructor
  · intro hu
    by_contra hne
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · have := (h s).2.mpr hneg
      simp only [hu] at this
      exact lt_irrefl 0 this
    · have := (h s).1.mpr hpos
      simp only [hu] at this
      exact lt_irrefl 0 this
  · intro hv
    by_contra hne
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · have := (h s).2.mp hneg
      simp only [hv] at this
      exact lt_irrefl 0 this
    · have := (h s).1.mp hpos
      simp only [hv] at this
      exact lt_irrefl 0 this

omit [DecidableEq S] in
/-- **The class pairing of a log-ratio with the sign pattern of the class direction is
positive.** -/
theorem classPairing_pos_of_sameSign {v μ : S → ℝ} (hv : v ≠ 0) (h : SameSign μ v) :
    0 < classPairing v μ := by
  have hz : ∀ s, v s = 0 ↔ μ s = 0 := fun s => (sameSign_zero_iff h s).symm
  have hnonneg : ∀ s, 0 ≤ v s * μ s := by
    intro s
    rcases lt_trichotomy (v s) 0 with hneg | heq | hpos
    · have hμ : μ s < 0 := (h s).2.mpr hneg
      exact mul_nonneg_of_nonpos_of_nonpos hneg.le hμ.le
    · have hμ : μ s = 0 := (hz s).mp heq
      rw [heq, hμ]
      simp
    · have hμ : 0 < μ s := (h s).1.mpr hpos
      exact (mul_pos hpos hμ).le
  obtain ⟨s, hs⟩ := Function.ne_iff.mp hv
  have hs0 : v s ≠ 0 := by
    intro hs0
    simp only [Pi.zero_apply] at hs
    exact hs hs0
  have hμs : μ s ≠ 0 := by
    intro hμs
    exact hs0 ((hz s).2 hμs)
  have hstrict : 0 < v s * μ s := by
    rcases lt_or_gt_of_ne hμs with hμneg | hμpos
    · have hvneg : v s < 0 := (h s).2.mp hμneg
      exact mul_pos_of_neg_of_neg hvneg hμneg
    · have hvpos : 0 < v s := (h s).1.mp hμpos
      exact mul_pos hvpos hμpos
  have hle : v s * μ s ≤ ∑ t, v t * μ t :=
    Finset.single_le_sum (fun i _ => hnonneg i) (Finset.mem_univ s)
  exact lt_of_lt_of_le hstrict hle

/-- **In a rank-one network the algorithm's linear inequality system is implied by the sign
compatibility**: the whole Deficiency One Algorithm for a rank-one network reduces to the
feasibility of the two scalar flux balances. -/
theorem rankOne_pairingOrder_of_sameSign (N : Network S) (v : S → ℝ) (hv : v ≠ 0)
    (hspan : N.stoichSubspace = Submodule.span ℝ {v}) (μ : S → ℝ) (h : SameSign μ v) :
    N.RankOnePairingOrder v hv hspan μ := by
  exact (N.rankOne_pairingOrder_iff v hv hspan μ).mpr
    (ne_of_gt (classPairing_pos_of_sameSign hv h))

/-! ### The algorithm in the classical deficiency-one setting -/

/-- **The Deficiency One Algorithm for a deficiency-one network: a feasible system yields the
capacity for multiple steady states.**

This is the shape of Feinberg's theorem in the classical setting — a deficiency-one network
(`hdef1`), of stoichiometric rank one (`hrank1`) with a one-dimensional stoichiometric subspace
(`hspan`) — and the conclusion holds.  The proof does not need the structural hypotheses: the
feasibility test is correct for every network, and the rank-one specialization
`rankOne_hasMultistationarityCapacity_iff` spells the test out in the reduced coordinates in
which Feinberg's numerical version runs it. -/
theorem doa_feasible_implies_capacity (N : Network S) (hdef1 : N.deficiencyInt = 1)
    (hrank1 : N.stoichRank = 1) (v : S → ℝ) (hv : v ≠ 0)
    (hspan : N.stoichSubspace = Submodule.span ℝ {v}) (hfeas : N.DOAFeasible) :
    N.HasMultistationarityCapacity := by
  -- a deficiency-one network of stoichiometric rank one has two more complexes than linkage
  -- classes: `n − ℓ − s = 1` with `s = 1` gives `n = ℓ + 2`.
  have hcomplexes : N.numComplexes = N.numLinkageClasses + 2 := by
    have h2 : (N.stoichRank : ℤ) = 1 := by exact_mod_cast hrank1
    have h1 : (N.numComplexes : ℤ) - (N.numLinkageClasses : ℤ) - (N.stoichRank : ℤ) = 1 := hdef1
    omega
  -- the stoichiometric subspace is the line `span {v}`
  have hne : N.stoichSubspace ≠ ⊥ := by
    rw [hspan]
    exact (Submodule.ne_bot_iff _).mpr ⟨v, Submodule.mem_span_singleton_self v, hv⟩
  -- in the rank-one setting the general system is the rank-one system
  have hsys : N.RankOneDOASystem v hv hspan := (N.rankOne_doaFeasible_iff v hv hspan).mp hfeas
  exact N.rankOne_doaFeasible_implies_capacity v hv hspan hsys

/-! ### A family on which the test is decided -/

/-- **The capacity of the fully open network is the existence of two distinct positive steady
states**: the fully open extension has the whole species space as its stoichiometric subspace, so
every two positive concentrations lie in one compatibility class. -/
theorem hasMultistationarityCapacity_iff_twoSteadyStates_of_fullyOpen (N : Network S) :
    N.fullyOpen.HasMultistationarityCapacity ↔
      ∃ (κ : N.fullyOpen.RateConstants) (x z : Concentration S),
        x.Positive ∧ z.Positive ∧ x ≠ z ∧ N.fullyOpen.IsMassActionSteadyState κ x ∧
          N.fullyOpen.IsMassActionSteadyState κ z := by
  constructor
  · rintro ⟨κ, x₀, x, y, hx, hy, hsx, hsy, hne⟩
    exact ⟨κ, x, y, hx.2, hy.2, hne, hsx, hsy⟩
  · rintro ⟨κ, x, z, hx, hz, hne, hsx, hsz⟩
    refine ⟨κ, x, x, z, ⟨StoichCompatible.refl N.fullyOpen x, hx⟩, ⟨?_, hz⟩, hsx, hsz, hne⟩
    rw [StoichCompatible, stoichSubspace_fullyOpen_eq_top]
    exact Submodule.mem_top

/-- **The Deficiency One Algorithm on the fully open network with a single non-flow reaction
`a → b`.**  The test is feasible exactly when `∑_{b_i > a_i} a_i > 1` (Joshi 2013, Theorem 4.1);
the algorithm is therefore correct on this family. -/
theorem oneRxn_doaFeasible_iff (a b : Complex S) :
    (oneRxn a b).fullyOpen.DOAFeasible ↔ 1 < ∑ s ∈ univ.filter (fun s => a s < b s), a s := by
  have h1 : (oneRxn a b).fullyOpen.DOAFeasible ↔
      (oneRxn a b).fullyOpen.HasMultistationarityCapacity :=
    (oneRxn a b).fullyOpen.hasMultistationarityCapacity_iff_doaFeasible.symm
  have h2 : (oneRxn a b).fullyOpen.HasMultistationarityCapacity ↔
      ∃ (κ : (oneRxn a b).fullyOpen.RateConstants) (x z : Concentration S),
        x.Positive ∧ z.Positive ∧ x ≠ z ∧ (oneRxn a b).fullyOpen.IsMassActionSteadyState κ x ∧
          (oneRxn a b).fullyOpen.IsMassActionSteadyState κ z :=
    (oneRxn a b).hasMultistationarityCapacity_iff_twoSteadyStates_of_fullyOpen
  exact h1.trans (h2.trans (oneRxn_multistationary_iff a b))

end Network
end CRNT
