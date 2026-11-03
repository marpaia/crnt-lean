import CRNT.Dynamics.TierExtraction
import CRNT.Dynamics.TierLyapunov
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Sequences

/-!
# Simultaneous extraction of tier subsequences

This file formalizes Remark 4.1 from the tier proof.  The key observation is that the network has
finitely many *occurrences* of complexes (one source and one target occurrence for each reaction).
For a positive sequence `xₙ`, collect every pairwise monomial ratio into one point of the finite
product

`((N.R × Bool) × (N.R × Bool)) → ℝ≥0∞`.

That product is compact.  Hence one subsequence makes all pairwise ratios converge
simultaneously.  A coordinate limit equal to `0`, a finite positive number, or `∞` gives,
respectively, a strict lower-tier relation, a same-tier relation, or the reverse strict relation.
This is exactly the total asymptotic preorder required by `IsTierSequence`.
-/

open Filter Set
open scoped BigOperators Topology ENNReal

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- A finite slot containing either the source or target occurrence of a reaction.  Duplicate
complexes are harmless; using occurrences avoids introducing a separate finite-type wrapper for
`N.complexes`. -/
abbrev TierComplexSlot (N : Network S) := N.R × Bool

/-- Complex represented by a source/target slot. -/
def tierComplexAtSlot (N : Network S) : N.TierComplexSlot → Complex S
  | (r, false) => (N.reaction r).source
  | (r, true) => (N.reaction r).target

/-- Every occurring complex has at least one finite source/target slot. -/
theorem exists_tierComplexSlot_of_mem_complexes (N : Network S) {y : Complex S}
    (hy : y ∈ N.complexes) :
    ∃ a : N.TierComplexSlot, N.tierComplexAtSlot a = y := by
  rw [complexes, Finset.mem_union] at hy
  rcases hy with hsrc | htgt
  · rcases Finset.mem_image.mp hsrc with ⟨r, _hrmem, hr⟩
    refine ⟨(r, false), ?_⟩
    simpa [tierComplexAtSlot] using hr
  · rcases Finset.mem_image.mp htgt with ⟨r, _hrmem, hr⟩
    refine ⟨(r, true), ?_⟩
    simpa [tierComplexAtSlot] using hr

/-- Positive real ratio of two tier monomials.

`noncomputable` because real division is. -/
noncomputable def tierRatioReal (xs : ℕ → Concentration S) (n : ℕ) (y y' : Complex S) : ℝ :=
  tierMonomial (xs n) y / tierMonomial (xs n) y'

/-- The same ratio, embedded in the compact extended nonnegative reals. -/
noncomputable def tierRatioENNReal (xs : ℕ → Concentration S) (n : ℕ)
    (y y' : Complex S) : ℝ≥0∞ :=
  ENNReal.ofReal (tierRatioReal xs n y y')

/-- Every tier ratio is strictly positive along a positive sequence. -/
theorem tierRatioReal_pos {xs : ℕ → Concentration S} (hpos : PositiveSequence xs)
    (n : ℕ) (y y' : Complex S) : 0 < tierRatioReal xs n y y' := by
  unfold tierRatioReal
  have hy : 0 < tierMonomial (xs n) y := by
    simpa [tierMonomial_eq_massActionMonomial] using
      Complex.massActionMonomial_pos (hpos n) y
  have hy' : 0 < tierMonomial (xs n) y' := by
    simpa [tierMonomial_eq_massActionMonomial] using
      Complex.massActionMonomial_pos (hpos n) y'
  exact div_pos hy hy'

/-- Simultaneous vector of every pairwise ratio between finite source/target occurrences. -/
noncomputable def tierRatioVector (N : Network S) (xs : ℕ → Concentration S) (n : ℕ) :
    (N.TierComplexSlot × N.TierComplexSlot) → ℝ≥0∞ :=
  fun ab => tierRatioENNReal xs n (N.tierComplexAtSlot ab.1) (N.tierComplexAtSlot ab.2)

/-- Strict tier comparison read back from convergence of an extended ratio to zero. -/
theorem tierStrictBelow_of_ennrealRatio_tendsto_zero
    {xs : ℕ → Concentration S} (hpos : PositiveSequence xs)
    (y y' : Complex S)
    (h : Tendsto (fun n => tierRatioENNReal xs n y y') atTop (𝓝 0)) :
    TierStrictBelow xs y y' := by
  have hreal := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp h
  unfold TierStrictBelow
  change Tendsto (fun n => tierRatioReal xs n y y') atTop (𝓝 0)
  convert hreal using 1
  · funext n
    simp only [tierRatioENNReal, Function.comp_apply]
    rw [ENNReal.toReal_ofReal (tierRatioReal_pos hpos n y y').le]
  · simp

/-- Same-tier comparison read back from convergence to a finite positive extended ratio. -/
theorem tierSame_of_ennrealRatio_tendsto_finite
    {xs : ℕ → Concentration S} (hpos : PositiveSequence xs)
    (y y' : Complex S) {c : ℝ≥0∞} (hc0 : c ≠ 0) (hctop : c ≠ ∞)
    (h : Tendsto (fun n => tierRatioENNReal xs n y y') atTop (𝓝 c)) :
    TierSame xs y y' := by
  refine ⟨c.toReal, ENNReal.toReal_pos hc0 hctop, ?_⟩
  have hreal := (ENNReal.tendsto_toReal hctop).comp h
  change Tendsto (fun n => tierRatioReal xs n y y') atTop (𝓝 c.toReal)
  convert hreal using 1
  funext n
  simp only [tierRatioENNReal, Function.comp_apply]
  rw [ENNReal.toReal_ofReal (tierRatioReal_pos hpos n y y').le]

/-- If the forward ratio tends to infinity, the reverse ratio tends to zero. -/
theorem tierStrictBelow_reverse_of_ennrealRatio_tendsto_top
    {xs : ℕ → Concentration S} (hpos : PositiveSequence xs)
    (y y' : Complex S)
    (h : Tendsto (fun n => tierRatioENNReal xs n y y') atTop (𝓝 ∞)) :
    TierStrictBelow xs y' y := by
  have hatTop : Tendsto (fun n => tierRatioReal xs n y y') atTop atTop := by
    exact ENNReal.tendsto_ofReal_nhds_top.mp h
  have hinv : Tendsto (fun n => (tierRatioReal xs n y y')⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hatTop
  unfold TierStrictBelow tierRatioReal at *
  simpa only [inv_div] using hinv

/-- Strictly increasing subsequences preserve positivity. -/
theorem PositiveSequence.comp (h : PositiveSequence (S := S) xs) (φ : ℕ → ℕ) :
    PositiveSequence (xs ∘ φ) :=
  fun n => h (φ n)

/-- Any cofinal subsequence preserves logarithmic escape. -/
theorem LogEscapes.comp_strictMono {xs : ℕ → Concentration S} (hesc : LogEscapes xs)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) : LogEscapes (xs ∘ φ) := by
  intro R
  obtain ⟨N, hN⟩ := hesc R
  have hev : ∀ᶠ n in atTop, N ≤ φ n :=
    hφ.tendsto_atTop (eventually_ge_atTop N)
  rw [eventually_atTop] at hev
  obtain ⟨M, hM⟩ := hev
  refine ⟨M, ?_⟩
  intro n hn
  simpa [Function.comp_apply] using hN (φ n) (hM n hn)

/-- **Remark 4.1.** Every positive logarithmically escaping sequence has a tier subsequence. -/
theorem everyPositiveLogEscapingSequenceHasTierSubsequence (N : Network S) :
    N.EveryPositiveLogEscapingSequenceHasTierSubsequence := by
  intro xs hpos hesc
  let q : ℕ → (N.TierComplexSlot × N.TierComplexSlot) → ℝ≥0∞ :=
    fun n => N.tierRatioVector xs n
  obtain ⟨L, _hLuniv, φ, hφ, hlim⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set ((N.TierComplexSlot × N.TierComplexSlot) → ℝ≥0∞))).tendsto_subseq
      (x := q) (fun _ => Set.mem_univ _)
  refine ⟨φ, hφ, ?_⟩
  refine ⟨hpos.comp φ, hesc.comp_strictMono hφ, ?_⟩
  intro y hy y' hy'
  obtain ⟨a, ha⟩ := N.exists_tierComplexSlot_of_mem_complexes hy
  obtain ⟨b, hb⟩ := N.exists_tierComplexSlot_of_mem_complexes hy'
  have hcoord0 := (tendsto_pi_nhds.mp hlim) (a, b)
  have hcoord :
      Tendsto (fun n => tierRatioENNReal (xs ∘ φ) n y y') atTop (𝓝 (L (a, b))) := by
    -- `(xs ∘ φ) n` and `xs (φ n)` are definitionally equal, but `simpa` will not bridge the
    -- two lambda bodies on its own; state the identification and rewrite.
    have hfun : (fun n => tierRatioENNReal (xs ∘ φ) n y y')
        = fun i => tierRatioENNReal xs (φ i) y y' := rfl
    rw [hfun]
    simpa [q, tierRatioVector, Function.comp_apply, ha, hb] using hcoord0
  by_cases hzero : L (a, b) = 0
  · left
    left
    apply tierStrictBelow_of_ennrealRatio_tendsto_zero (hpos.comp φ) y y'
    simpa [hzero] using hcoord
  · by_cases htop : L (a, b) = ∞
    · right
      apply tierStrictBelow_reverse_of_ennrealRatio_tendsto_top (hpos.comp φ) y y'
      simpa [htop] using hcoord
    · left
      right
      exact tierSame_of_ennrealRatio_tendsto_finite (hpos.comp φ) y y' hzero htop hcoord

/-- Public proposition-valued API is discharged unconditionally by Remark 4.1. -/
theorem everyPositiveLogEscapingSequenceHasTierSubsequence_claim (N : Network S) :
    N.EveryPositiveLogEscapingSequenceHasTierSubsequence :=
  N.everyPositiveLogEscapingSequenceHasTierSubsequence

end Network
end CRNT
