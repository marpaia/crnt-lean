import CRNT.Basic.Network
import CRNT.Stoich.Vector
import CRNT.Subnetwork.ReactionRestriction
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-!
# Tropical model reduction (Samal et al.)

This module formalizes the tropical reduction procedure for mass-action reaction
networks.  Given rate constants scaled by powers of a small parameter,
`κ_r = κ̄_r ε^{a_r}`, and a valuation `w` (concentrations scale as
`x_s ≈ ε^{w_s}`), each reaction `r` carries a *tropical order*
`a_r + ⟨source_r, w⟩`.  A *tropical equilibration* at `w` means that for every
species changed by some reaction, the minimum of these orders over the reactions
changing that species is attained by both a producing and a consuming reaction
(see `CRNT.Algebra.TropicalEquilibration`, in particular
`Network.tropicalEquilibration_of_steadyStates`).

The reduction keeps exactly the reactions that are *tropically minimal* for at
least one species they change.  This module defines that set
(`tropicalReduced`), proves that under an equilibration it changes the same set
of species as the full network (`tropicalReduced_species_eq`), and that the
leading (tropical) system is unchanged by the reduction
(`leadingSystem_eq_reduced_of_equilibration`).

Relation to leaf A4: this completes the "tropical reduction procedure of Samal
et al." item left open in `CRNT/Algebra/TropicalEquilibration.lean`.  The
converse direction (tropical equilibrations determine nearby steady states) is
handled by `CRNT.Algebra.TropicalLifting`.

* `tropicalOrder` — tropical order `a_r + ⟨source_r, w⟩` of a reaction.
* `IsTropicalEquilibration` — network-level equilibration predicate (mirroring
  the conclusion of `Network.tropicalEquilibration_of_steadyStates`).
* `tropicalReduced` — Finset of tropically minimal reactions.
* `tropicalLeadingSystem` — Finset of reactions attaining the minimal order for
  (at least one of) the species they change.
-/

namespace CRNT

namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

noncomputable def tropicalOrder (N : Network S) (a : N.R → ℝ) (w : S → ℝ)
    (r : N.R) : ℝ :=
  a r + ∑ s : S, ((N.reaction r).source s : ℝ) * w s

def IsTropicalEquilibration (N : Network S) (a : N.R → ℝ) (w : S → ℝ) : Prop :=
  ∀ s : S, (∃ r : N.R, N.reactionVector r s ≠ 0) →
    ∃ r₁ r₂ : N.R, 0 < N.reactionVector r₁ s ∧ N.reactionVector r₂ s < 0 ∧
      ∀ r : N.R, N.reactionVector r s ≠ 0 →
        tropicalOrder N a w r₁ ≤ tropicalOrder N a w r ∧
        tropicalOrder N a w r₂ ≤ tropicalOrder N a w r

noncomputable def tropicalReduced (N : Network S) (a : N.R → ℝ) (w : S → ℝ) :
    Finset N.R :=
  Finset.univ.filter fun r =>
    ∃ s : S, N.reactionVector r s ≠ 0 ∧
      ∀ r' : N.R, N.reactionVector r' s ≠ 0 →
        tropicalOrder N a w r ≤ tropicalOrder N a w r'

noncomputable def tropicalLeadingSystem (N : Network S) (a : N.R → ℝ) (w : S → ℝ) :
    Finset N.R :=
  Finset.univ.filter fun r =>
    ∃ s : S, N.reactionVector r s ≠ 0 ∧
      ∀ r' : N.R, N.reactionVector r' s ≠ 0 →
        tropicalOrder N a w r ≤ tropicalOrder N a w r'

theorem tropicalReduced_mem (N : Network S) (a : N.R → ℝ) (w : S → ℝ) (r : N.R) :
    r ∈ tropicalReduced N a w ↔
      ∃ s : S, N.reactionVector r s ≠ 0 ∧
        ∀ r' : N.R, N.reactionVector r' s ≠ 0 →
          tropicalOrder N a w r ≤ tropicalOrder N a w r' := by
  classical
  constructor
  · intro hr
    exact (Finset.mem_filter.mp hr).2
  · intro h
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩

theorem tropicalLeadingSystem_mem (N : Network S) (a : N.R → ℝ) (w : S → ℝ)
    (r : N.R) :
    r ∈ tropicalLeadingSystem N a w ↔
      ∃ s : S, N.reactionVector r s ≠ 0 ∧
        ∀ r' : N.R, N.reactionVector r' s ≠ 0 →
          tropicalOrder N a w r ≤ tropicalOrder N a w r' := by
  classical
  constructor
  · intro hr
    exact (Finset.mem_filter.mp hr).2
  · intro h
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩

theorem tropicalReduced_changes_subset (N : Network S) (a : N.R → ℝ) (w : S → ℝ) :
    {s : S | ∃ r ∈ tropicalReduced N a w, N.reactionVector r s ≠ 0} ⊆
      {s : S | ∃ r : N.R, N.reactionVector r s ≠ 0} := by
  intro s hs
  rcases hs with ⟨r, _, hrs⟩
  exact ⟨r, hrs⟩

theorem tropicalReduced_species_eq (N : Network S) (a : N.R → ℝ) (w : S → ℝ)
    (h : IsTropicalEquilibration N a w) :
    {s : S | ∃ r ∈ tropicalReduced N a w, N.reactionVector r s ≠ 0} =
      {s : S | ∃ r : N.R, N.reactionVector r s ≠ 0} := by
  ext s
  constructor
  · intro hs
    exact tropicalReduced_changes_subset N a w hs
  · intro hs
    rcases h s hs with ⟨r₁, _r₂, hr₁pos, _hr₂neg, hmin⟩
    have hr₁changes : N.reactionVector r₁ s ≠ 0 := hr₁pos.ne'
    have hr₁red : r₁ ∈ tropicalReduced N a w := by
      rw [tropicalReduced_mem]
      exact ⟨s, hr₁changes, fun r' hr' => (hmin r' hr').1⟩
    exact ⟨r₁, hr₁red, hr₁changes⟩

theorem leadingSystem_subset_reduced (N : Network S) (a : N.R → ℝ) (w : S → ℝ) :
    tropicalLeadingSystem N a w ⊆ tropicalReduced N a w := by
  intro r hr
  exact hr

theorem leadingSystem_eq_reduced_of_equilibration (N : Network S) (a : N.R → ℝ)
    (w : S → ℝ) (_h : IsTropicalEquilibration N a w) :
    (tropicalLeadingSystem (N.restrictReactions (tropicalReduced N a w))
        (fun r => a r.1) w).image Subtype.val =
      tropicalLeadingSystem N a w := by
  classical
  set E := tropicalReduced N a w with hE
  ext r
  constructor
  · intro hr
    rcases Finset.mem_image.mp hr with ⟨r', _hr', rfl⟩
    exact r'.2
  · intro hr
    have hrE : r ∈ E := leadingSystem_subset_reduced N a w hr
    rcases (tropicalReduced_mem N a w r).mp hrE with ⟨s, hrs, hminfull⟩
    have hlead : (⟨r, hrE⟩ : (N.restrictReactions E).R) ∈
        tropicalLeadingSystem (N.restrictReactions E) (fun r => a r.1) w := by
      unfold tropicalLeadingSystem
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_univ _
      · refine ⟨s, ?_, ?_⟩
        · rw [show (N.restrictReactions E).reactionVector ⟨r, hrE⟩ s =
              N.reactionVector r s from
            congrFun (restrictReactions_reactionVector N E ⟨r, hrE⟩) s]
          exact hrs
        · intro r' hr'
          have hr's : N.reactionVector r'.1 s ≠ 0 := by
            simpa [restrictReactions_reactionVector] using hr'
          exact hminfull r'.1 hr's
    exact Finset.mem_image.mpr ⟨⟨r, hrE⟩, hlead, rfl⟩

end Network

namespace TropicalReductionInstance

open Network

abbrev SEx := Fin 2
abbrev REx := Fin 3

def exSource : REx → (SEx → ℕ)
  | 0 => fun s => if s = 0 then 1 else 0
  | 1 => fun s => if s = 1 then 1 else 0
  | 2 => fun s => if s = 0 then 1 else 0

def exTarget : REx → (SEx → ℕ)
  | 0 => fun s => if s = 1 then 1 else 0
  | 1 => fun s => if s = 0 then 1 else 0
  | 2 => fun s => if s = 1 then 1 else 0

def exNetwork : Network SEx where
  R := REx
  decEqR := inferInstance
  fintypeR := inferInstance
  reaction := fun r => ⟨exSource r, exTarget r⟩

def exA : REx → ℝ
  | 0 => 0
  | 1 => 0
  | 2 => 1

def exW : SEx → ℝ := fun _ => 0

theorem ex_isEquil : Network.IsTropicalEquilibration exNetwork exA exW := by
  classical
  intro s hs
  -- species 0 (X)
  by_cases hs0 : s = (0 : SEx)
  · subst hs0
    refine ⟨(1 : REx), (0 : REx), ?_, ?_, ?_⟩
    · simp [Network.reactionVector_apply, exNetwork, exSource, exTarget]
    · simp [Network.reactionVector_apply, exNetwork, exSource, exTarget]
    · intro r hr
      rcases r with ⟨i, hi⟩
      interval_cases i
      · constructor
        · simp [Network.tropicalOrder, exA, exW, exNetwork, exSource]
        · simp [Network.tropicalOrder, exA, exW, exNetwork, exSource]
      · constructor
        · simp [Network.tropicalOrder, exA, exW, exNetwork, exSource]
        · simp [Network.tropicalOrder, exA, exW, exNetwork, exSource]
      · constructor
        · simp [Network.tropicalOrder, exA, exW, exNetwork, exSource]
        · simp [Network.tropicalOrder, exA, exW, exNetwork, exSource]
  -- species 1 (Y)
  · have hs1 : s = (1 : SEx) := by
      rcases s with ⟨j, hj⟩
      have hj0 : j ≠ 0 := by
        intro h
        apply hs0
        exact Fin.eq_of_val_eq h
      have : j = 1 := by omega
      exact Fin.eq_of_val_eq this
    subst hs1
    refine ⟨(0 : REx), (1 : REx), ?_, ?_, ?_⟩
    · simp [Network.reactionVector_apply, exNetwork, exSource, exTarget]
    · simp [Network.reactionVector_apply, exNetwork, exSource, exTarget]
    · intro r hr
      rcases r with ⟨i, hi⟩
      interval_cases i
      · constructor
        · simp [Network.tropicalOrder, exA, exW, exNetwork, exSource]
        · simp [Network.tropicalOrder, exA, exW, exNetwork, exSource]
      · constructor
        · simp [Network.tropicalOrder, exA, exW, exNetwork, exSource]
        · simp [Network.tropicalOrder, exA, exW, exNetwork, exSource]
      · constructor
        · simp [Network.tropicalOrder, exA, exW, exNetwork, exSource]
        · simp [Network.tropicalOrder, exA, exW, exNetwork, exSource]

theorem ex_species_eq :
    {s : SEx | ∃ r ∈ Network.tropicalReduced exNetwork exA exW,
        exNetwork.reactionVector r s ≠ 0} =
    {s : SEx | ∃ r : exNetwork.R, exNetwork.reactionVector r s ≠ 0} := by
  exact Network.tropicalReduced_species_eq exNetwork exA exW ex_isEquil

theorem ex_leading_eq :
    (Network.tropicalLeadingSystem
        (exNetwork.restrictReactions (Network.tropicalReduced exNetwork exA exW))
        (fun r => exA r.1) exW).image Subtype.val =
      Network.tropicalLeadingSystem exNetwork exA exW := by
  exact Network.leadingSystem_eq_reduced_of_equilibration exNetwork exA exW ex_isEquil

end TropicalReductionInstance

end CRNT
