import CRNT.Oscillation.Basic

/-!
# Reaction restriction, minimal oscillatory subnetworks, and inheritance interfaces

Oscillation arguments often identify a smaller reaction set responsible for a dynamical behavior and
then ask whether that behavior survives network enlargement.  This module supplies the exact finite
subnetwork object and deliberately separates two claims that should not be conflated:

1. a reaction-restricted network has oscillatory capacity;
2. an enlargement preserves that capacity.

The second is *not* automatic for strictly positive mass-action rate constants.  It therefore appears
as an explicit `OscillationPreserving` proposition rather than an unsound monotonicity theorem.
Unlike the first checkpoint, the preservation relation is polymorphic in the species type, because
important CRN inheritance theorems add new species as well as reactions.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Restrict a network to a finite subset of its reaction channels. -/
def restrictOscillationReactions (N : Network S) (rs : Finset N.R) : Network S where
  R := {r : N.R // r ∈ rs}
  decEqR := inferInstance
  fintypeR := inferInstance
  reaction r := N.reaction r.1

@[simp] theorem restrictReactions_numReactions (N : Network S) (rs : Finset N.R) :
    (N.restrictOscillationReactions rs).numReactions = rs.card := by
  change Fintype.card (↥rs) = rs.card
  exact Fintype.card_coe rs

/-- A minimal reaction-restricted subnetwork with oscillatory capacity.

This is a generic formal notion of a *minimal oscillatory subnetwork*.  It should not be confused
with any stronger paper-specific stoichiometric characterization of an "oscillatory core" until the
corresponding structural theorem is formalized. -/
structure MinimalOscillatorySubnetwork (N : Network S) where
  /-- Reactions retained by the subnetwork. -/
  reactions : Finset N.R
  /-- The core is nonempty. -/
  nonempty : reactions.Nonempty
  /-- The restricted network has oscillatory capacity. -/
  capable : (N.restrictOscillationReactions reactions).OscillatoryCapacity
  /-- Removing any retained reaction destroys the certified capacity. -/
  minimal : ∀ r ∈ reactions,
    ¬ (N.restrictOscillationReactions (reactions.erase r)).OscillatoryCapacity

/-- A behavior-preserving network transformation at the level of oscillatory capacity.

The source and target may use different species types; this is necessary for inheritance results that
add new species. -/
def OscillationPreserving
    {S₁ S₂ : Type} [DecidableEq S₁] [Fintype S₁] [DecidableEq S₂] [Fintype S₂]
    (N₁ : Network S₁) (N₂ : Network S₂) : Prop :=
  N₁.OscillatoryCapacity → N₂.OscillatoryCapacity

/-- Two networks are equivalent with respect to oscillatory capacity. -/
def OscillationEquivalent
    {S₁ S₂ : Type} [DecidableEq S₁] [Fintype S₁] [DecidableEq S₂] [Fintype S₂]
    (N₁ : Network S₁) (N₂ : Network S₂) : Prop :=
  N₁.OscillatoryCapacity ↔ N₂.OscillatoryCapacity

/-- Identity preserves oscillatory capacity. -/
theorem oscillationPreserving_refl (N : Network S) : N.OscillationPreserving N :=
  fun h => h

/-- Oscillation-preserving transformations compose, including across species-type changes. -/
theorem OscillationPreserving.trans
    {S₁ S₂ S₃ : Type}
    [DecidableEq S₁] [Fintype S₁]
    [DecidableEq S₂] [Fintype S₂]
    [DecidableEq S₃] [Fintype S₃]
    {N₁ : Network S₁} {N₂ : Network S₂} {N₃ : Network S₃}
    (h₁₂ : N₁.OscillationPreserving N₂) (h₂₃ : N₂.OscillationPreserving N₃) :
    N₁.OscillationPreserving N₃ :=
  fun h => h₂₃ (h₁₂ h)

/-- Oscillation equivalence is reflexive. -/
theorem oscillationEquivalent_refl (N : Network S) : N.OscillationEquivalent N :=
  Iff.rfl

/-- Oscillation equivalence is symmetric. -/
theorem OscillationEquivalent.symm
    {S₁ S₂ : Type} [DecidableEq S₁] [Fintype S₁] [DecidableEq S₂] [Fintype S₂]
    {N₁ : Network S₁} {N₂ : Network S₂}
    (h : N₁.OscillationEquivalent N₂) : N₂.OscillationEquivalent N₁ :=
  Iff.symm h

/-- Oscillation equivalence is transitive. -/
theorem OscillationEquivalent.trans
    {S₁ S₂ S₃ : Type}
    [DecidableEq S₁] [Fintype S₁]
    [DecidableEq S₂] [Fintype S₂]
    [DecidableEq S₃] [Fintype S₃]
    {N₁ : Network S₁} {N₂ : Network S₂} {N₃ : Network S₃}
    (h₁₂ : N₁.OscillationEquivalent N₂) (h₂₃ : N₂.OscillationEquivalent N₃) :
    N₁.OscillationEquivalent N₃ :=
  Iff.trans h₁₂ h₂₃

/-- Equivalence gives preservation in the forward direction. -/
theorem OscillationEquivalent.toPreserving
    {S₁ S₂ : Type} [DecidableEq S₁] [Fintype S₁] [DecidableEq S₂] [Fintype S₂]
    {N₁ : Network S₁} {N₂ : Network S₂}
    (h : N₁.OscillationEquivalent N₂) : N₁.OscillationPreserving N₂ :=
  h.mp

/-- Equivalence also gives preservation in the reverse direction. -/
theorem OscillationEquivalent.toPreservingSymm
    {S₁ S₂ : Type} [DecidableEq S₁] [Fintype S₁] [DecidableEq S₂] [Fintype S₂]
    {N₁ : Network S₁} {N₂ : Network S₂}
    (h : N₁.OscillationEquivalent N₂) : N₂.OscillationPreserving N₁ :=
  h.mpr

/-- Structural non-oscillation pulls backwards along an oscillation-preserving transformation.
If every oscillatory realization of `N₁` would induce one in `N₂`, then proving `N₂` can never
oscillate also proves that `N₁` can never oscillate. -/
theorem neverPositivePeriodic_of_preserving
    {S₁ S₂ : Type} [DecidableEq S₁] [Fintype S₁] [DecidableEq S₂] [Fintype S₂]
    {N₁ : Network S₁} {N₂ : Network S₂}
    (hpres : N₁.OscillationPreserving N₂) (hnever : N₂.NeverPositivePeriodic) :
    N₁.NeverPositivePeriodic := by
  rw [N₁.neverPositivePeriodic_iff_not_oscillatoryCapacity]
  intro hcap
  have hcap₂ : N₂.OscillatoryCapacity := hpres hcap
  exact (N₂.neverPositivePeriodic_iff_not_oscillatoryCapacity.mp hnever) hcap₂

/-- Oscillation-equivalent networks are equivalent for structural non-oscillation as well. -/
theorem OscillationEquivalent.neverPositivePeriodic_iff
    {S₁ S₂ : Type} [DecidableEq S₁] [Fintype S₁] [DecidableEq S₂] [Fintype S₂]
    {N₁ : Network S₁} {N₂ : Network S₂}
    (h : N₁.OscillationEquivalent N₂) :
    N₁.NeverPositivePeriodic ↔ N₂.NeverPositivePeriodic := by
  rw [N₁.neverPositivePeriodic_iff_not_oscillatoryCapacity,
    N₂.neverPositivePeriodic_iff_not_oscillatoryCapacity]
  exact not_congr h

/-- If an oscillatory network embeds into a larger network through a separately proven
capacity-preserving extension, the larger network has oscillatory capacity.  The preservation proof
is intentionally explicit: arbitrary reaction/species addition is not assumed monotone. -/
theorem oscillatoryCapacity_of_preserving_extension
    {S₁ S₂ : Type} [DecidableEq S₁] [Fintype S₁] [DecidableEq S₂] [Fintype S₂]
    {Nsmall : Network S₁} {Nlarge : Network S₂}
    (hsmall : Nsmall.OscillatoryCapacity)
    (hext : Nsmall.OscillationPreserving Nlarge) :
    Nlarge.OscillatoryCapacity :=
  hext hsmall

/-- A chain of capacity-preserving transformations transports an oscillatory-capacity certificate. -/
theorem oscillatoryCapacity_of_preserving_chain
    {S₁ S₂ S₃ : Type}
    [DecidableEq S₁] [Fintype S₁]
    [DecidableEq S₂] [Fintype S₂]
    [DecidableEq S₃] [Fintype S₃]
    {N₁ : Network S₁} {N₂ : Network S₂} {N₃ : Network S₃}
    (hcap : N₁.OscillatoryCapacity)
    (h₁₂ : N₁.OscillationPreserving N₂)
    (h₂₃ : N₂.OscillationPreserving N₃) :
    N₃.OscillatoryCapacity :=
  h₂₃ (h₁₂ hcap)

end Network

end CRNT
