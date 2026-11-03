import CRNT.Deficiency.KernelDimension
import CRNT.LinearAlgebra.OrthogonalComplement

/-!
# Buffering structures and influence indices

This module formalizes the structural objects used in the topological robustness theory
of Okada--Mochizuki and Hirono--Gupta--Khammash, together with the strong-buffering
flux index of Hong--Moon--Hirono--Kim.

Only the mathematics of the CRN is represented here: subnetworks, output completeness,
the supported cycle space, the projected conservation-law space, and the two influence
indices.  No numerical enumeration or steady-state solver is involved.

For a subnetwork `γ = (Vγ,Eγ)`, output completeness uses the **any substrate** rule:
if a species in `Vγ` occurs with nonzero coefficient in the source complex of a reaction,
that reaction must lie in `Eγ`.

The influence indices are

`λ(γ)   = -|Vγ| + |Eγ| - dim ker(S)|_{Eγ} + dim P⁰_γ(coker S)`

and

`λ_f(γ) = -|Vγ| + |Eγ|                    + dim P⁰_γ(coker S)`.

The identity `λ_f = λ + dim ker(S)|_{Eγ}` is proved exactly.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- A structural subnetwork is specified by a set of species and a set of reaction
channels.  We intentionally do not require reaction endpoints to be complexes entirely
supported on the species set: output-complete subnetworks in buffering theory are not
induced subnetworks in that graph-theoretic sense. -/
structure StructuralSubnetwork (N : Network S) where
  species : Finset S
  reactions : Finset N.R

namespace StructuralSubnetwork

variable {N : Network S}

/-- Componentwise inclusion of structural subnetworks. -/
def LE (γ η : StructuralSubnetwork N) : Prop :=
  γ.species ⊆ η.species ∧ γ.reactions ⊆ η.reactions

/-- Componentwise union. -/
def union (γ η : StructuralSubnetwork N) : StructuralSubnetwork N where
  species := γ.species ∪ η.species
  reactions := γ.reactions ∪ η.reactions

/-- Componentwise intersection. -/
def inter (γ η : StructuralSubnetwork N) : StructuralSubnetwork N where
  species := γ.species ∩ η.species
  reactions := γ.reactions ∩ η.reactions

/-- The empty structural subnetwork. -/
def bot (N : Network S) : StructuralSubnetwork N where
  species := ∅
  reactions := ∅

/-- The full structural subnetwork. -/
def top (N : Network S) : StructuralSubnetwork N where
  species := Finset.univ
  reactions := Finset.univ

@[simp] theorem species_union (γ η : StructuralSubnetwork N) :
    (γ.union η).species = γ.species ∪ η.species := rfl

@[simp] theorem reactions_union (γ η : StructuralSubnetwork N) :
    (γ.union η).reactions = γ.reactions ∪ η.reactions := rfl

@[simp] theorem species_inter (γ η : StructuralSubnetwork N) :
    (γ.inter η).species = γ.species ∩ η.species := rfl

@[simp] theorem reactions_inter (γ η : StructuralSubnetwork N) :
    (γ.inter η).reactions = γ.reactions ∩ η.reactions := rfl

end StructuralSubnetwork

/-- A reaction *reads* a species when that species occurs as a reactant, i.e. with
nonzero coefficient in the source complex. -/
def ReactionReadsSpecies (N : Network S) (r : N.R) (s : S) : Prop :=
  (N.reaction r).source s ≠ 0

/-- A structural subnetwork is **output-complete** if every reaction whose rate can
respond directly to one of its species is included among its reactions.  For mass-action
kinetics this means every reaction with at least one reactant in `γ.species` is in
`γ.reactions`. -/
def IsOutputComplete (N : Network S) (γ : StructuralSubnetwork N) : Prop :=
  ∀ r : N.R, ∀ s : S,
    s ∈ γ.species → N.ReactionReadsSpecies r s → r ∈ γ.reactions

/-- The empty subnetwork is output-complete. -/
theorem outputComplete_bot (N : Network S) :
    N.IsOutputComplete (StructuralSubnetwork.bot N) := by
  intro r s hs
  simp [StructuralSubnetwork.bot] at hs

/-- The full subnetwork is output-complete. -/
theorem outputComplete_top (N : Network S) :
    N.IsOutputComplete (StructuralSubnetwork.top N) := by
  intro r s hs hread
  simp [StructuralSubnetwork.top]

/-- Output-complete subnetworks are closed under componentwise union. -/
theorem IsOutputComplete.union (N : Network S) {γ η : StructuralSubnetwork N}
    (hγ : N.IsOutputComplete γ) (hη : N.IsOutputComplete η) :
    N.IsOutputComplete (γ.union η) := by
  intro r s hs hread
  simp only [StructuralSubnetwork.species_union, Finset.mem_union] at hs
  simp only [StructuralSubnetwork.reactions_union, Finset.mem_union]
  rcases hs with hs | hs
  · exact Or.inl (hγ r s hs hread)
  · exact Or.inr (hη r s hs hread)

/-- Output-complete subnetworks are closed under componentwise intersection. -/
theorem IsOutputComplete.inter (N : Network S) {γ η : StructuralSubnetwork N}
    (hγ : N.IsOutputComplete γ) (hη : N.IsOutputComplete η) :
    N.IsOutputComplete (γ.inter η) := by
  intro r s hs hread
  simp only [StructuralSubnetwork.species_inter, Finset.mem_inter] at hs
  simp only [StructuralSubnetwork.reactions_inter, Finset.mem_inter]
  exact ⟨hγ r s hs.1 hread, hη r s hs.2 hread⟩

/-- Reaction-coordinate vectors supported entirely on the selected reaction set `E`. -/
def supportedReactionSubspace (N : Network S) (E : Finset N.R) :
    Submodule ℝ (N.R → ℝ) where
  carrier := {v | ∀ r, r ∉ E → v r = 0}
  zero_mem' := by intro r hr; rfl
  add_mem' := by
    intro v w hv hw r hr
    simp [hv r hr, hw r hr]
  smul_mem' := by
    intro a v hv r hr
    simp [hv r hr]

@[simp] theorem mem_supportedReactionSubspace (N : Network S) (E : Finset N.R)
    (v : N.R → ℝ) :
    v ∈ N.supportedReactionSubspace E ↔ ∀ r, r ∉ E → v r = 0 := Iff.rfl

/-- Stoichiometric cycles supported inside the reaction set of `γ`.
This is `(ker S)_{supp γ}` in the buffering-structure literature. -/
noncomputable def supportedCycleSubspace (N : Network S) (γ : StructuralSubnetwork N) :
    Submodule ℝ (N.R → ℝ) :=
  LinearMap.ker N.stoichMap ⊓ N.supportedReactionSubspace γ.reactions

/-- Restriction of a species vector to a selected finite set of species. -/
def speciesRestriction (V : Finset S) : (S → ℝ) →ₗ[ℝ] (↥V → ℝ) where
  toFun w := fun s => w s.1
  map_add' x y := rfl
  map_smul' a x := rfl

@[simp] theorem speciesRestriction_apply (V : Finset S) (w : S → ℝ) (s : ↥V) :
    speciesRestriction V w s = w s.1 := rfl

/-- Conservation laws projected to the selected species coordinates.

`orthSum N.stoichSubspace` is the left nullspace/cokernel of the stoichiometric map;
mapping it through coordinate restriction gives `P⁰_γ(coker S)`. -/
def projectedConservationSubspace (N : Network S) (γ : StructuralSubnetwork N) :
    Submodule ℝ (↥γ.species → ℝ) :=
  (orthSum N.stoichSubspace).map (speciesRestriction γ.species)

/-- Dimension of the supported stoichiometric cycle space. -/
noncomputable def supportedCycleDim (N : Network S) (γ : StructuralSubnetwork N) : ℕ :=
  Module.finrank ℝ (N.supportedCycleSubspace γ)

/-- Dimension of the projected conservation-law space `P⁰_γ(coker S)`. -/
noncomputable def projectedConservationDim (N : Network S)
    (γ : StructuralSubnetwork N) : ℕ :=
  Module.finrank ℝ (N.projectedConservationSubspace γ)

/-- Hirono--Gupta--Khammash influence index.  It is integer-valued because the
cardinality terms enter with opposite signs. -/
noncomputable def influenceIndex (N : Network S) (γ : StructuralSubnetwork N) : ℤ :=
  -(γ.species.card : ℤ) + (γ.reactions.card : ℤ)
    - (N.supportedCycleDim γ : ℤ) + (N.projectedConservationDim γ : ℤ)

/-- Hong--Moon--Hirono--Kim flux influence index. -/
noncomputable def fluxInfluenceIndex (N : Network S) (γ : StructuralSubnetwork N) : ℤ :=
  -(γ.species.card : ℤ) + (γ.reactions.card : ℤ)
    + (N.projectedConservationDim γ : ℤ)

/-- The exact algebraic relation between the two topological indices. -/
theorem fluxInfluenceIndex_eq_influenceIndex_add_supportedCycleDim
    (N : Network S) (γ : StructuralSubnetwork N) :
    N.fluxInfluenceIndex γ =
      N.influenceIndex γ + (N.supportedCycleDim γ : ℤ) := by
  simp [fluxInfluenceIndex, influenceIndex]
  ring

/-- A buffering structure is output-complete and has vanishing influence index. -/
def IsBufferingStructure (N : Network S) (γ : StructuralSubnetwork N) : Prop :=
  N.IsOutputComplete γ ∧ N.influenceIndex γ = 0

/-- A strong buffering structure is output-complete and has vanishing flux influence
index.  The global flux-RPA theorem can be layered on top of this structural predicate. -/
def IsStrongBufferingStructure (N : Network S) (γ : StructuralSubnetwork N) : Prop :=
  N.IsOutputComplete γ ∧ N.fluxInfluenceIndex γ = 0

/-- Every buffering structure is output-complete. -/
theorem IsBufferingStructure.outputComplete (N : Network S) {γ : StructuralSubnetwork N}
    (h : N.IsBufferingStructure γ) : N.IsOutputComplete γ := h.1

/-- Every strong buffering structure is output-complete. -/
theorem IsStrongBufferingStructure.outputComplete (N : Network S)
    {γ : StructuralSubnetwork N} (h : N.IsStrongBufferingStructure γ) :
    N.IsOutputComplete γ := h.1

/-- For a strong buffering structure, the ordinary influence index is the negative of
its supported-cycle dimension.  The literature's stronger implication to ordinary
buffering additionally uses the nonnegativity theorem for output-complete influence
indices; that theorem is intentionally not assumed here. -/
theorem influenceIndex_eq_neg_supportedCycleDim_of_strong
    (N : Network S) {γ : StructuralSubnetwork N} (h : N.IsStrongBufferingStructure γ) :
    N.influenceIndex γ = -(N.supportedCycleDim γ : ℤ) := by
  have hid := N.fluxInfluenceIndex_eq_influenceIndex_add_supportedCycleDim γ
  rw [h.2] at hid
  omega

end Network
end CRNT
