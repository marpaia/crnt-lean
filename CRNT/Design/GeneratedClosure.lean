import CRNT.Design.OutputCompleteClosure

/-!
# Joint output/reactant closure of a structural subnetwork

The seed construction used in buffering-structure and RPA analyses alternates two closure
requirements:

* if a species is included, every reaction reading it must be included (output completeness);
* if a reaction is included, every reactant species of that reaction must be included.

Rather than formalizing an implementation-specific loop, this file defines the **least**
subnetwork satisfying both requirements as the intersection of all closed extensions.
The construction is finite, canonical, idempotent, and basis-independent.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Reactant closure: every reactant of an included reaction is an included species. -/
def IsReactantClosed (N : Network S) (γ : StructuralSubnetwork N) : Prop :=
  ∀ r : N.R, r ∈ γ.reactions → ∀ s : S,
    N.ReactionReadsSpecies r s → s ∈ γ.species

/-- Joint structural closure used by generated buffering subnetworks. -/
def IsGeneratedClosed (N : Network S) (γ : StructuralSubnetwork N) : Prop :=
  N.IsOutputComplete γ ∧ N.IsReactantClosed γ

/-- The full subnetwork is jointly closed. -/
theorem generatedClosed_top (N : Network S) :
    N.IsGeneratedClosed (StructuralSubnetwork.top N) := by
  refine ⟨N.outputComplete_top, ?_⟩
  intro r hr s hs
  simp [StructuralSubnetwork.top]

/-- Joint closure is stable under intersections. -/
theorem IsGeneratedClosed.inter (N : Network S) {γ η : StructuralSubnetwork N}
    (hγ : N.IsGeneratedClosed γ) (hη : N.IsGeneratedClosed η) :
    N.IsGeneratedClosed (γ.inter η) := by
  constructor
  · exact hγ.1.inter N hη.1
  · intro r hr s hread
    simp only [StructuralSubnetwork.reactions_inter, Finset.mem_inter] at hr
    simp only [StructuralSubnetwork.species_inter, Finset.mem_inter]
    exact ⟨hγ.2 r hr.1 s hread, hη.2 r hr.2 s hread⟩

/-- Species belonging to every jointly closed extension of the seed. -/
noncomputable def generatedSpecies (N : Network S) (seed : StructuralSubnetwork N) : Finset S := by
  classical
  exact Finset.univ.filter fun s =>
    ∀ η : StructuralSubnetwork N,
      StructuralSubnetwork.LE seed η → N.IsGeneratedClosed η → s ∈ η.species

/-- Reactions belonging to every jointly closed extension of the seed. -/
noncomputable def generatedReactions (N : Network S) (seed : StructuralSubnetwork N) :
    Finset N.R := by
  classical
  exact Finset.univ.filter fun r =>
    ∀ η : StructuralSubnetwork N,
      StructuralSubnetwork.LE seed η → N.IsGeneratedClosed η → r ∈ η.reactions

/-- Canonical least joint closure. -/
noncomputable def generatedClosure (N : Network S) (seed : StructuralSubnetwork N) :
    StructuralSubnetwork N where
  species := N.generatedSpecies seed
  reactions := N.generatedReactions seed

/-- The seed is contained in its generated closure. -/
theorem le_generatedClosure (N : Network S) (seed : StructuralSubnetwork N) :
    StructuralSubnetwork.LE seed (N.generatedClosure seed) := by
  classical
  constructor
  · intro s hs
    simp [generatedClosure, generatedSpecies]
    intro η hle hclosed
    exact hle.1 hs
  · intro r hr
    simp [generatedClosure, generatedReactions]
    intro η hle hclosed
    exact hle.2 hr

/-- The generated closure is output-complete. -/
theorem generatedClosure_outputComplete (N : Network S) (seed : StructuralSubnetwork N) :
    N.IsOutputComplete (N.generatedClosure seed) := by
  classical
  intro r s hs hread
  simp only [generatedClosure, generatedSpecies, Finset.mem_filter, Finset.mem_univ,
    true_and] at hs
  simp only [generatedClosure, generatedReactions, Finset.mem_filter, Finset.mem_univ,
    true_and]
  intro η hle hclosed
  exact hclosed.1 r s (hs η hle hclosed) hread

/-- The generated closure is reactant-closed. -/
theorem generatedClosure_reactantClosed (N : Network S) (seed : StructuralSubnetwork N) :
    N.IsReactantClosed (N.generatedClosure seed) := by
  classical
  intro r hr s hread
  simp only [generatedClosure, generatedReactions, Finset.mem_filter, Finset.mem_univ,
    true_and] at hr
  simp only [generatedClosure, generatedSpecies, Finset.mem_filter, Finset.mem_univ,
    true_and]
  intro η hle hclosed
  exact hclosed.2 r (hr η hle hclosed) s hread

/-- The generated closure is jointly closed. -/
theorem generatedClosure_closed (N : Network S) (seed : StructuralSubnetwork N) :
    N.IsGeneratedClosed (N.generatedClosure seed) :=
  ⟨N.generatedClosure_outputComplete seed, N.generatedClosure_reactantClosed seed⟩

/-- **Universal minimality.** The generated closure lies in every jointly closed extension. -/
theorem generatedClosure_le (N : Network S) {seed η : StructuralSubnetwork N}
    (hle : StructuralSubnetwork.LE seed η) (hη : N.IsGeneratedClosed η) :
    StructuralSubnetwork.LE (N.generatedClosure seed) η := by
  classical
  constructor
  · intro s hs
    simp only [generatedClosure, generatedSpecies, Finset.mem_filter, Finset.mem_univ,
      true_and] at hs
    exact hs η hle hη
  · intro r hr
    simp only [generatedClosure, generatedReactions, Finset.mem_filter, Finset.mem_univ,
      true_and] at hr
    exact hr η hle hη

/-- Generated closure is monotone. -/
theorem generatedClosure_mono (N : Network S) {γ η : StructuralSubnetwork N}
    (hγη : StructuralSubnetwork.LE γ η) :
    StructuralSubnetwork.LE (N.generatedClosure γ) (N.generatedClosure η) := by
  apply N.generatedClosure_le
  · exact ⟨
      fun s hs => (N.le_generatedClosure η).1 (hγη.1 hs),
      fun r hr => (N.le_generatedClosure η).2 (hγη.2 hr)⟩
  · exact N.generatedClosure_closed η

/-- Generated closure is idempotent. -/
theorem generatedClosure_idem (N : Network S) (γ : StructuralSubnetwork N) :
    N.generatedClosure (N.generatedClosure γ) = N.generatedClosure γ := by
  apply StructuralSubnetwork.ext
  · apply Finset.Subset.antisymm
    · exact (N.generatedClosure_le
        (⟨Finset.Subset.refl _, Finset.Subset.refl _⟩ :
          StructuralSubnetwork.LE (N.generatedClosure γ) (N.generatedClosure γ))
        (N.generatedClosure_closed γ)).1
    · exact (N.le_generatedClosure (N.generatedClosure γ)).1
  · apply Finset.Subset.antisymm
    · exact (N.generatedClosure_le
        (⟨Finset.Subset.refl _, Finset.Subset.refl _⟩ :
          StructuralSubnetwork.LE (N.generatedClosure γ) (N.generatedClosure γ))
        (N.generatedClosure_closed γ)).2
    · exact (N.le_generatedClosure (N.generatedClosure γ)).2

/-- Fixed points of generated closure are precisely jointly closed subnetworks. -/
theorem isGeneratedClosed_iff_generatedClosure_eq (N : Network S)
    (γ : StructuralSubnetwork N) :
    N.IsGeneratedClosed γ ↔ N.generatedClosure γ = γ := by
  constructor
  · intro h
    apply StructuralSubnetwork.ext
    · exact Finset.Subset.antisymm
        (N.generatedClosure_le (show StructuralSubnetwork.LE γ γ from ⟨fun _ h => h, fun _ h => h⟩) h).1
        (N.le_generatedClosure γ).1
    · exact Finset.Subset.antisymm
        (N.generatedClosure_le (show StructuralSubnetwork.LE γ γ from ⟨fun _ h => h, fun _ h => h⟩) h).2
        (N.le_generatedClosure γ).2
  · intro h
    rw [← h]
    exact N.generatedClosure_closed γ

end Network

end CRNT
