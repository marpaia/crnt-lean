import CRNT.Translation.ReactionTranslation

/-!
# Source-complex maps of a reaction translation

The proper/improper distinction in network translation concerns source complexes rather
than all complexes.  This file packages the finite source sets and source fibres induced
by a translation.
-/

namespace CRNT
namespace Network
namespace ReactionTranslation

variable {S : Type} [DecidableEq S] [Fintype S]
variable {N : Network S}

/-- Original source complexes. -/
def originalSourceComplexes (T : N.ReactionTranslation) : Finset (Complex S) :=
  Finset.univ.image fun r : N.R => (N.reaction r).source

/-- Translated source complexes. -/
def translatedSourceComplexes (T : N.ReactionTranslation) : Finset (Complex S) :=
  Finset.univ.image fun r : N.R => T.source r

/-- Reactions whose translated source is `c`. -/
def sourceFiber (T : N.ReactionTranslation) (c : Complex S) : Finset N.R :=
  Finset.univ.filter fun r => T.source r = c

@[simp] theorem mem_sourceFiber_iff (T : N.ReactionTranslation) (c : Complex S) (r : N.R) :
    r ∈ T.sourceFiber c ↔ T.source r = c := by
  simp [sourceFiber]

/-- A translated source is represented by at least one reaction. -/
theorem exists_reaction_of_mem_translatedSourceComplexes
    (T : N.ReactionTranslation) {c : Complex S}
    (hc : c ∈ T.translatedSourceComplexes) :
    ∃ r : N.R, T.source r = c := by
  simpa [translatedSourceComplexes] using hc

/-- Source coherence says original-source equality descends to the translated source map. -/
theorem source_eq_implies_translatedSource_eq
    (T : N.ReactionTranslation) (h : T.SourceCoherent)
    {r q : N.R} (hrq : (N.reaction r).source = (N.reaction q).source) :
    T.source r = T.source q := h r q hrq

/-- Properness makes translated-source equality equivalent to original-source equality. -/
theorem proper_source_eq_iff (T : N.ReactionTranslation) (h : T.Proper)
    (r q : N.R) :
    T.source r = T.source q ↔ (N.reaction r).source = (N.reaction q).source := by
  exact h r q

/-- An improper source merger: two distinct original source complexes have been identified
by the translated graph. -/
def HasImproperSourceMerge (T : N.ReactionTranslation) : Prop :=
  ∃ r q : N.R,
    (N.reaction r).source ≠ (N.reaction q).source ∧ T.source r = T.source q

/-- A proper translation has no improper source merger. -/
theorem noImproperSourceMerge_of_proper (T : N.ReactionTranslation)
    (h : T.Proper) : ¬ T.HasImproperSourceMerge := by
  rintro ⟨r, q, hne, heq⟩
  exact hne ((h r q).1 heq)

/-- For a source-coherent translation, absence of source merging is exactly properness. -/
theorem proper_iff_sourceCoherent_and_noMerge (T : N.ReactionTranslation) :
    T.Proper ↔ T.SourceCoherent ∧ ¬ T.HasImproperSourceMerge := by
  constructor
  · intro h
    refine ⟨?_, T.noImproperSourceMerge_of_proper h⟩
    intro r q heq
    exact (h r q).2 heq
  · rintro ⟨hcoh, hnomerge⟩
    intro r q
    constructor
    · intro heq
      by_contra hsrc
      exact hnomerge ⟨r, q, hsrc, heq⟩
    · exact hcoh r q

/-- Proper translation induces a bijection between the finite sets of original and
translated source complexes. -/
theorem card_translatedSourceComplexes_eq_of_proper
    (T : N.ReactionTranslation) (h : T.Proper) :
    T.translatedSourceComplexes.card = T.originalSourceComplexes.card := by
  classical
  let rep : ∀ c : Complex S, c ∈ T.translatedSourceComplexes → N.R :=
    fun c hc => Classical.choose (T.exists_reaction_of_mem_translatedSourceComplexes hc)
  have hrep : ∀ c hc, T.source (rep c hc) = c := by
    intro c hc
    exact Classical.choose_spec (T.exists_reaction_of_mem_translatedSourceComplexes hc)
  apply Finset.card_bij
    (fun c hc => (N.reaction (rep c hc)).source)
  · intro c hc
    simp only [originalSourceComplexes, Finset.mem_image]
    exact ⟨rep c hc, Finset.mem_univ _, rfl⟩
  · intro c hc d hd heq
    have htrans : T.source (rep c hc) = T.source (rep d hd) :=
      (h (rep c hc) (rep d hd)).2 heq
    rw [hrep c hc, hrep d hd] at htrans
    exact htrans
  · intro b hb
    simp only [originalSourceComplexes, Finset.mem_image] at hb
    rcases hb with ⟨r, -, rfl⟩
    have hc : T.source r ∈ T.translatedSourceComplexes := by
      simp [translatedSourceComplexes]
    refine ⟨T.source r, hc, ?_⟩
    have hsrc : (N.reaction (rep (T.source r) hc)).source = (N.reaction r).source :=
      (h (rep (T.source r) hc) r).1 ?_
    · exact hsrc
    · exact (hrep (T.source r) hc).trans rfl

end ReactionTranslation
end Network
end CRNT
