import CRNT.Dynamics.TierSubsequenceExtraction
import CRNT.Dynamics.ProperTierTransversal

/-!
# Completed tier extraction for one stoichiometric class

This module closes the two finite-dimensional inputs used by the compact-negativity reduction:

* Remark 4.1: positive logarithmically escaping sequences admit tier subsequences;
* Lemma 4.1: proper tier sequences are transversal.

A sequence contained in one positive stoichiometric compatibility class has a proper tier
subsequence automatically, so these theorems give the exact transversal extraction property used
by `TierSequentialReduction` without additional hypotheses.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Every logarithmically escaping sequence inside one positive stoichiometric class has a
transversal tier subsequence. -/
theorem everyEscapingClassSequenceHasTransversalTierSubsequence (N : Network S) :
    N.EveryEscapingClassSequenceHasTransversalTierSubsequence := by
  exact N.everyEscapingClassSequenceHasTransversalTierSubsequence_of_tierExtraction
    N.everyPositiveLogEscapingSequenceHasTierSubsequence
    N.properTierSequencesAreTransversal

/-- Once uniform Proposition 4.6 is available, the completed finite extraction theory gives the
compact negative-dissipation region of Corollary 5.1 directly. -/
theorem exists_compact_class_region_negative_outside_of_uniformTierNegativity
    (N : Network S) (hneg : N.UniformTierDissipationEventuallyNegative)
    (xref : Concentration S) (δ : ℝ) :
    ∃ K : Set (Concentration S), IsCompact K ∧
      K ⊆ N.positiveCompatibilityClass xref ∧
      ∀ (k : N.R → ℝ) (x : Concentration S),
        N.RateVectorInBand δ k → x ∈ N.positiveCompatibilityClass xref → x ∉ K →
          N.tierDissipationWith k x < 0 := by
  exact N.exists_compact_class_region_negative_outside_of_tier_inputs
    N.everyEscapingClassSequenceHasTransversalTierSubsequence hneg xref δ

end Network
end CRNT
