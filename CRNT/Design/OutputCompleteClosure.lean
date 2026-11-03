import CRNT.Design.BufferingStructure

/-!
# Least output-complete closure of a structural subnetwork

For a chosen species set `V`, output completeness forces inclusion of every reaction
whose rate law reads at least one species of `V`.  This module makes that forcing
operation canonical.  It defines the finite set of required reactions and proves that
adjoining precisely those reactions is the **least output-complete extension** that
leaves the species set unchanged.

This is the structural closure used implicitly by labeled-buffering-structure theory.
It contains no response-matrix sampling or numerical perturbation machinery.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

@[ext] theorem StructuralSubnetwork.ext {N : Network S} {γ η : StructuralSubnetwork N}
    (hs : γ.species = η.species) (hr : γ.reactions = η.reactions) : γ = η := by
  cases γ
  cases η
  simp_all

/-- All reaction channels forced by output completeness for a set of species `V`:
those that read at least one species of `V` in their source complex. -/
noncomputable def requiredReactions (N : Network S) (V : Finset S) : Finset N.R := by
  classical
  exact Finset.univ.filter fun r => ∃ s ∈ V, N.ReactionReadsSpecies r s

@[simp] theorem mem_requiredReactions (N : Network S) (V : Finset S) (r : N.R) :
    r ∈ N.requiredReactions V ↔ ∃ s ∈ V, N.ReactionReadsSpecies r s := by
  classical
  simp [requiredReactions]

/-- The reactions that must still be added to `γ` to make it output-complete without
changing its species set. -/
noncomputable def missingOutputReactions (N : Network S) (γ : StructuralSubnetwork N) : Finset N.R :=
  N.requiredReactions γ.species \ γ.reactions

@[simp] theorem mem_missingOutputReactions (N : Network S)
    (γ : StructuralSubnetwork N) (r : N.R) :
    r ∈ N.missingOutputReactions γ ↔
      (∃ s ∈ γ.species, N.ReactionReadsSpecies r s) ∧ r ∉ γ.reactions := by
  simp [missingOutputReactions]

/-- Adjoin all reactions forced by the current species set.  The species set is left
unchanged. -/
noncomputable def outputCompleteClosure (N : Network S)
    (γ : StructuralSubnetwork N) : StructuralSubnetwork N where
  species := γ.species
  reactions := γ.reactions ∪ N.requiredReactions γ.species

@[simp] theorem outputCompleteClosure_species (N : Network S)
    (γ : StructuralSubnetwork N) :
    (N.outputCompleteClosure γ).species = γ.species := rfl

@[simp] theorem outputCompleteClosure_reactions (N : Network S)
    (γ : StructuralSubnetwork N) :
    (N.outputCompleteClosure γ).reactions =
      γ.reactions ∪ N.requiredReactions γ.species := rfl

/-- The closure is output-complete. -/
theorem outputComplete_outputCompleteClosure (N : Network S)
    (γ : StructuralSubnetwork N) :
    N.IsOutputComplete (N.outputCompleteClosure γ) := by
  intro r s hs hread
  simp only [outputCompleteClosure_species] at hs
  simp only [outputCompleteClosure_reactions, Finset.mem_union]
  exact Or.inr ((N.mem_requiredReactions γ.species r).2 ⟨s, hs, hread⟩)

/-- Every subnetwork is contained componentwise in its output-complete closure. -/
theorem le_outputCompleteClosure (N : Network S) (γ : StructuralSubnetwork N) :
    StructuralSubnetwork.LE γ (N.outputCompleteClosure γ) := by
  constructor
  · simp
  · intro r hr
    exact Finset.mem_union_left _ hr

/-- **Leastness of output-complete closure.** If `η` is output-complete and contains `γ`,
then it also contains the closure of `γ`. -/
theorem outputCompleteClosure_le (N : Network S) {γ η : StructuralSubnetwork N}
    (hγη : StructuralSubnetwork.LE γ η) (hη : N.IsOutputComplete η) :
    StructuralSubnetwork.LE (N.outputCompleteClosure γ) η := by
  constructor
  · simpa using hγη.1
  · intro r hr
    simp only [outputCompleteClosure_reactions, Finset.mem_union] at hr
    rcases hr with hr | hr
    · exact hγη.2 hr
    · obtain ⟨s, hsγ, hread⟩ := (N.mem_requiredReactions γ.species r).1 hr
      exact hη r s (hγη.1 hsγ) hread

/-- Output-complete closure is monotone under componentwise inclusion. -/
theorem outputCompleteClosure_mono (N : Network S) {γ η : StructuralSubnetwork N}
    (hγη : StructuralSubnetwork.LE γ η) :
    StructuralSubnetwork.LE (N.outputCompleteClosure γ) (N.outputCompleteClosure η) := by
  apply N.outputCompleteClosure_le
  · have hηc := N.le_outputCompleteClosure η
    exact ⟨fun s hs => hηc.1 (hγη.1 hs), fun r hr => hηc.2 (hγη.2 hr)⟩
  · exact N.outputComplete_outputCompleteClosure η

/-- Output-complete closure is idempotent. -/
theorem outputCompleteClosure_idem (N : Network S) (γ : StructuralSubnetwork N) :
    N.outputCompleteClosure (N.outputCompleteClosure γ) = N.outputCompleteClosure γ := by
  apply StructuralSubnetwork.ext
  · simp [outputCompleteClosure]
  · simp [outputCompleteClosure, Finset.union_assoc]

/-- A subnetwork is output-complete exactly when the closure operation fixes it. -/
theorem isOutputComplete_iff_outputCompleteClosure_eq (N : Network S)
    (γ : StructuralSubnetwork N) :
    N.IsOutputComplete γ ↔ N.outputCompleteClosure γ = γ := by
  constructor
  · intro h
    apply StructuralSubnetwork.ext
    · rfl
    · apply Finset.Subset.antisymm
      · intro r hr
        simp only [outputCompleteClosure_reactions, Finset.mem_union] at hr
        rcases hr with hr | hr
        · exact hr
        · obtain ⟨s, hs, hread⟩ := (N.mem_requiredReactions γ.species r).1 hr
          exact h r s hs hread
      · exact fun r hr => Finset.mem_union_left _ hr
  · intro h
    rw [← h]
    exact N.outputComplete_outputCompleteClosure γ

/-- Output completeness is equivalently inclusion of all required reactions. -/
theorem isOutputComplete_iff_required_subset (N : Network S)
    (γ : StructuralSubnetwork N) :
    N.IsOutputComplete γ ↔ N.requiredReactions γ.species ⊆ γ.reactions := by
  constructor
  · intro h r hr
    obtain ⟨s, hs, hread⟩ := (N.mem_requiredReactions γ.species r).1 hr
    exact h r s hs hread
  · intro h r s hs hread
    exact h ((N.mem_requiredReactions γ.species r).2 ⟨s, hs, hread⟩)

/-- No reaction already present in `γ` belongs to the set of reactions still missing. -/
theorem missingOutputReactions_disjoint (N : Network S)
    (γ : StructuralSubnetwork N) :
    Disjoint γ.reactions (N.missingOutputReactions γ) := by
  rw [Finset.disjoint_left]
  intro r hr hmissing
  exact ((N.mem_missingOutputReactions γ r).1 hmissing).2 hr

/-- The closure can equivalently be obtained by adjoining only the reactions not already
present. -/
theorem reactions_union_missingOutputReactions (N : Network S)
    (γ : StructuralSubnetwork N) :
    γ.reactions ∪ N.missingOutputReactions γ =
      (N.outputCompleteClosure γ).reactions := by
  ext r
  simp [missingOutputReactions, outputCompleteClosure]

end Network
end CRNT
