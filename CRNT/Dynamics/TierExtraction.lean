import CRNT.Dynamics.TierSequentialReduction

/-!
# Tier subsequence extraction and proper-to-transversal reduction

The deterministic compactness argument uses two finite-dimensional facts before Proposition 4.6:

* Remark 4.1: every positive logarithmically escaping sequence has a subsequence that is a tier
  sequence (there are only finitely many occurring complexes);
* Lemma 4.1: every proper tier sequence is transversal.

This module isolates these facts and proves all CRNT bookkeeping around them.  In particular, a
sequence contained in one positive stoichiometric compatibility class yields a *proper* tier
subsequence automatically, so the two generic facts imply the exact extraction API consumed by
`TierSequentialReduction`.
-/

open Filter
open scoped BigOperators Topology

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Remark-4.1-shaped finite extraction theorem. -/
def EveryPositiveLogEscapingSequenceHasTierSubsequence (N : Network S) : Prop :=
  ∀ xs : ℕ → Concentration S, PositiveSequence xs → LogEscapes xs →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ N.IsTierSequence (xs ∘ φ)

/-- Lemma-4.1-shaped theorem. -/
def ProperTierSequencesAreTransversal (N : Network S) : Prop :=
  ∀ xs : ℕ → Concentration S, N.IsProperTierSequence xs → N.IsTransversalTierSequence xs

/-- Points lying in one compatibility class differ by a stoichiometric-subspace vector. -/
theorem sub_mem_stoichSubspace_of_mem_same_compatibilityClass
    {N : Network S} {xref x y : Concentration S}
    (hx : x ∈ N.compatibilityClass xref) (hy : y ∈ N.compatibilityClass xref) :
    (x - y : Concentration S) ∈ N.stoichSubspace := by
  have hxy : N.StoichCompatible y x :=
    (show N.StoichCompatible xref y from hy).symm.trans
      (show N.StoichCompatible xref x from hx)
  simpa [StoichCompatible] using hxy

/-- Any tier subsequence of a sequence contained in one compatibility class is proper. -/
theorem isProperTierSequence_of_subsequence_in_class
    {N : Network S} {xref : Concentration S} {xs : ℕ → Concentration S}
    (hclass : ∀ n, xs n ∈ N.positiveCompatibilityClass xref)
    {φ : ℕ → ℕ} (htier : N.IsTierSequence (xs ∘ φ)) :
    N.IsProperTierSequence (xs ∘ φ) := by
  refine ⟨htier, ?_⟩
  intro n m
  exact N.sub_mem_stoichSubspace_of_mem_same_compatibilityClass
    (hclass (φ n)).1 (hclass (φ m)).1

/-- Remark 4.1 plus Lemma 4.1 give the exact transversal extraction statement needed by the
compact-negativity argument. -/
theorem everyEscapingClassSequenceHasTransversalTierSubsequence_of_tierExtraction
    {N : Network S}
    (hextract : N.EveryPositiveLogEscapingSequenceHasTierSubsequence)
    (hproper : N.ProperTierSequencesAreTransversal) :
    N.EveryEscapingClassSequenceHasTransversalTierSubsequence := by
  intro xref xs hclass hesc
  have hpos : PositiveSequence xs := fun n => (hclass n).2
  obtain ⟨φ, hφmono, htier⟩ := hextract xs hpos hesc
  refine ⟨φ, hφmono, ?_⟩
  apply hproper (xs ∘ φ)
  exact N.isProperTierSequence_of_subsequence_in_class hclass htier

/-- Combining tier extraction, proper=>transversal, and uniform Proposition 4.6 yields the compact
negative-dissipation region directly. -/
theorem exists_compact_class_region_negative_outside_of_tier_theorems
    {N : Network S}
    (hextract : N.EveryPositiveLogEscapingSequenceHasTierSubsequence)
    (hproper : N.ProperTierSequencesAreTransversal)
    (hneg : N.UniformTierDissipationEventuallyNegative)
    (xref : Concentration S) (δ : ℝ) :
    ∃ K : Set (Concentration S), IsCompact K ∧
      K ⊆ N.positiveCompatibilityClass xref ∧
      ∀ (k : N.R → ℝ) (x : Concentration S),
        N.RateVectorInBand δ k → x ∈ N.positiveCompatibilityClass xref → x ∉ K →
          N.tierDissipationWith k x < 0 := by
  apply N.exists_compact_class_region_negative_outside_of_tier_inputs
  · exact N.everyEscapingClassSequenceHasTransversalTierSubsequence_of_tierExtraction
      hextract hproper
  · exact hneg

end Network
end CRNT
