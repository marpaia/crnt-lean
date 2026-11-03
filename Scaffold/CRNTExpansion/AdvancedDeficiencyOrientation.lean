import CRNT.Translation.ParallelAggregation

/-!
# Orientation layer for the Advanced Deficiency Algorithm

The published Advanced Deficiency Algorithm starts by choosing an orientation of the reaction
set: every irreversible reaction is retained and, from each reversible pair, one direction is
chosen.  CRNT-Lean permits parallel channels, so the clean structural route is to apply this layer
to `N.mergeParallel`, where reaction channels are distinct directed reactions.

This file deliberately separates *orientation* from the later kernel-row colinearity machinery.
`AdvancedDeficiencyKernel` can consume the selected finite reaction set once an orientation is
available.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Two reaction channels are exact reverses when their endpoints are swapped.  Distinctness is
included so that a self-reaction is not its own reversible partner. -/
def ReverseChannels (N : Network S) (r q : N.R) : Prop :=
  r ≠ q ∧ (N.reaction r).source = (N.reaction q).target ∧
    (N.reaction r).target = (N.reaction q).source

@[symm] theorem ReverseChannels.symm {N : Network S} {r q : N.R}
    (h : N.ReverseChannels r q) : N.ReverseChannels q r := by
  rcases h with ⟨hrq, hs, ht⟩
  exact ⟨Ne.symm hrq, ht.symm, hs.symm⟩

/-- A channel is reversible at the graph level when an exact reverse channel occurs. -/
def HasReverseChannel (N : Network S) (r : N.R) : Prop :=
  ∃ q : N.R, N.ReverseChannels r q

/-- An irreversible channel has no exact reverse channel. -/
def IrreversibleChannel (N : Network S) (r : N.R) : Prop :=
  ¬ N.HasReverseChannel r

/-- A valid ADA orientation on a channel-level network.

For networks with parallel channels, use this structure on `N.mergeParallel`.  The `reverse_choice`
field says exactly one member of every reverse pair is selected; every irreversible channel is
selected. -/
structure ADAOrientation (N : Network S) where
  selected : Finset N.R
  irreversible_mem : ∀ r : N.R, N.IrreversibleChannel r → r ∈ selected
  reverse_choice : ∀ r q : N.R, N.ReverseChannels r q →
    (r ∈ selected ↔ q ∉ selected)

namespace ADAOrientation

variable {N : Network S}

/-- Reverse channels cannot both occur in a valid orientation. -/
theorem reverse_not_both (O : N.ADAOrientation) {r q : N.R}
    (hrev : N.ReverseChannels r q) : ¬ (r ∈ O.selected ∧ q ∈ O.selected) := by
  rintro ⟨hr, hq⟩
  exact (O.reverse_choice r q hrev).mp hr hq

/-- Every reversible pair contributes at least one direction to the orientation. -/
theorem reverse_mem_or_mem (O : N.ADAOrientation) {r q : N.R}
    (hrev : N.ReverseChannels r q) : r ∈ O.selected ∨ q ∈ O.selected := by
  by_cases hr : r ∈ O.selected
  · exact Or.inl hr
  · right
    by_contra hq
    exact hr ((O.reverse_choice r q hrev).mpr hq)

/-- Hence every reversible pair contributes exactly one selected channel. -/
theorem reverse_exactlyOne (O : N.ADAOrientation) {r q : N.R}
    (hrev : N.ReverseChannels r q) :
    (r ∈ O.selected ∨ q ∈ O.selected) ∧ ¬ (r ∈ O.selected ∧ q ∈ O.selected) :=
  ⟨O.reverse_mem_or_mem hrev, O.reverse_not_both hrev⟩

end ADAOrientation

/-- The parallel-safe ADA orientation type for an arbitrary CRNT network.  Parallel channels are
first merged, an operation already proved dynamically and structurally faithful by the translation
library. -/
abbrev ParallelReducedADAOrientation (N : Network S) := ADAOrientation N.mergeParallel

end Network
end CRNT
