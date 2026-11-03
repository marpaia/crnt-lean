import CRNT.Dynamics.TierCompactNegativity

/-!
# Sequential reduction for the tier compactness argument

The compact-negativity theorem needs one sequential exclusion statement.  This module factors that
statement into the two standard ingredients of the tier proof:

1. every logarithmically escaping sequence in one positive stoichiometric class has a transversal
   tier subsequence;
2. tier-descending systems have uniformly negative dissipation along every transversal tier
   sequence, even when the positive rate vector varies inside one compact band.

Once these are available, the compact bad-region exclusion follows formally.
-/

open Filter
open scoped BigOperators Topology

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The finite-dimensional tier extraction statement needed by Corollary 5.1.  The subsequence is
required to be transversal; because the original sequence lies in one compatibility class, this
packages both ordinary finite tier extraction and the proper-tier-sequence => transversal step. -/
def EveryEscapingClassSequenceHasTransversalTierSubsequence (N : Network S) : Prop :=
  ∀ (xref : Concentration S) (xs : ℕ → Concentration S),
    (∀ n, xs n ∈ N.positiveCompatibilityClass xref) →
    LogEscapes xs →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ N.IsTransversalTierSequence (xs ∘ φ)

/-- A fixed rate band is inherited by every subsequence. -/
theorem RateSequenceInBand.comp {N : Network S} {δ : ℝ} {ks : ℕ → N.R → ℝ}
    (h : N.RateSequenceInBand δ ks) (φ : ℕ → ℕ) :
    N.RateSequenceInBand δ (ks ∘ φ) := by
  refine ⟨h.1, ?_⟩
  intro n r
  exact h.2 (φ n) r

/-- **Tier extraction + uniform Proposition 4.6 imply sequential exclusion.** -/
theorem noEscapingNonnegativeDissipationOnClass_of_tierSubsequence_and_uniformNegativity
    {N : Network S}
    (hextract : N.EveryEscapingClassSequenceHasTransversalTierSubsequence)
    (hneg : N.UniformTierDissipationEventuallyNegative)
    (xref : Concentration S) (δ : ℝ) :
    N.NoEscapingNonnegativeDissipationOnClass xref δ := by
  intro ks xs hband hclass hesc
  obtain ⟨φ, hφmono, hφtier⟩ := hextract xref xs hclass hesc
  have hbandφ : N.RateSequenceInBand δ (ks ∘ φ) := hband.comp φ
  have hunifφ : N.UniformPositiveRateSequence (ks ∘ φ) := Network.rateSequenceInBand_uniformPositive hbandφ
  obtain ⟨n₀, hn₀⟩ := hneg (ks ∘ φ) hunifφ (xs ∘ φ) hφtier
  refine ⟨φ n₀, ?_⟩
  simpa [Function.comp_apply] using hn₀ n₀ le_rfl

/-- The two tier inputs therefore yield one compact positive class region outside of which every
rate vector in the chosen band has negative dissipation. -/
theorem exists_compact_class_region_negative_outside_of_tier_inputs
    {N : Network S}
    (hextract : N.EveryEscapingClassSequenceHasTransversalTierSubsequence)
    (hneg : N.UniformTierDissipationEventuallyNegative)
    (xref : Concentration S) (δ : ℝ) :
    ∃ K : Set (Concentration S), IsCompact K ∧
      K ⊆ N.positiveCompatibilityClass xref ∧
      ∀ (k : N.R → ℝ) (x : Concentration S),
        N.RateVectorInBand δ k → x ∈ N.positiveCompatibilityClass xref → x ∉ K →
          N.tierDissipationWith k x < 0 := by
  apply N.exists_compact_class_region_negative_outside_of_noEscaping
  exact N.noEscapingNonnegativeDissipationOnClass_of_tierSubsequence_and_uniformNegativity
    hextract hneg xref δ

end Network
end CRNT
