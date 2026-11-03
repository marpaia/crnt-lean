import CRNT.Translation.SourceCoefficientEquivalence
import CRNT.Stoich.Subspace

/-!
# Aggregating parallel reaction channels

Parallel reactions have identical source and target complexes and hence identical
mass-action monomials and reaction vectors.  Their only dynamical effect is through the
sum of their rate constants.  This module packages that elementary but useful realization
invariance without erasing parallel channels from the core `Network` representation.
-/

namespace CRNT
namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Two channels are parallel when they represent the same directed reaction. -/
def Parallel {N : Network S} (r q : N.R) : Prop := N.reaction r = N.reaction q

/-- Total rate constant carried by all channels realizing a particular directed
reaction. -/
def aggregateRate (N : Network S) (κ : N.RateConstants) (ρ : Reaction S) : ℝ :=
  ∑ r : N.R, if N.reaction r = ρ then κ.k r else 0

/-- Aggregate rates are nonnegative. -/
theorem aggregateRate_nonneg (N : Network S) (κ : N.RateConstants) (ρ : Reaction S) :
    0 ≤ N.aggregateRate κ ρ := by
  unfold aggregateRate
  apply Finset.sum_nonneg
  intro r _
  by_cases h : N.reaction r = ρ
  · simp [h, (κ.positive r).le]
  · simp [h]

/-- An actually occurring reaction has a strictly positive aggregate rate. -/
theorem aggregateRate_pos_of_occurs (N : Network S) (κ : N.RateConstants)
    (ρ : Reaction S) (hρ : ∃ r : N.R, N.reaction r = ρ) :
    0 < N.aggregateRate κ ρ := by
  rcases hρ with ⟨r, hr⟩
  unfold aggregateRate
  apply Finset.sum_pos'
  · intro q _
    by_cases hq : N.reaction q = ρ
    · simp [hq, (κ.positive q).le]
    · simp [hq]
  · refine ⟨r, Finset.mem_univ r, ?_⟩
    simp [hr, κ.positive r]

/-- The finite set of distinct directed reactions realized by the network. -/
def distinctReactions (N : Network S) : Finset (Reaction S) :=
  Finset.univ.image N.reaction

/-- Network obtained by merging parallel channels. -/
def mergeParallel (N : Network S) : Network S where
  R := {ρ : Reaction S // ρ ∈ N.distinctReactions}
  decEqR := inferInstance
  fintypeR := inferInstance
  reaction := fun ρ => ρ.1

/-- Aggregate rate constants on the merged network. -/
noncomputable def mergedRateConstants (N : Network S) (κ : N.RateConstants) :
    (N.mergeParallel).RateConstants where
  k := fun ρ => N.aggregateRate κ ρ.1
  positive := fun ρ => by
    apply N.aggregateRate_pos_of_occurs κ ρ.1
    rcases Finset.mem_image.mp ρ.2 with ⟨r, _, hr⟩
    exact ⟨r, hr⟩

/-- Merging parallel channels preserves every source coefficient. -/
theorem mergeParallel_sourceCoefficient
    (N : Network S) (κ : N.RateConstants) (y : Complex S) :
    (N.mergeParallel).sourceCoefficient (N.mergedRateConstants κ) y =
      N.sourceCoefficient κ y := by
  classical
  funext s
  unfold sourceCoefficient
  have hsubtype :
      (∑ ρ : {ρ : Reaction S // ρ ∈ N.distinctReactions},
        if ρ.1.source = y then
          N.aggregateRate κ ρ.1 * N.mergeParallel.reactionVector ρ s else 0) =
      ∑ ρ ∈ N.distinctReactions,
        if ρ.source = y then N.aggregateRate κ ρ * ρ.vector s else 0 := by
    symm
    exact Finset.sum_subtype N.distinctReactions (fun ρ => Iff.rfl)
      (fun ρ => if ρ.source = y then N.aggregateRate κ ρ * ρ.vector s else 0)
  change (∑ ρ : {ρ : Reaction S // ρ ∈ N.distinctReactions},
      if ρ.1.source = y then
        N.aggregateRate κ ρ.1 * N.mergeParallel.reactionVector ρ s else 0) =
    ∑ r : N.R, if (N.reaction r).source = y then κ.k r * N.reactionVector r s else 0
  rw [hsubtype]
  have hfiber : ∀ ρ ∈ N.distinctReactions,
      (if ρ.source = y then N.aggregateRate κ ρ * ρ.vector s else 0) =
      ∑ r ∈ Finset.univ with N.reaction r = ρ,
        (if (N.reaction r).source = y then κ.k r * N.reactionVector r s else 0) := by
    intro ρ hρ
    by_cases hy : ρ.source = y
    · have hagg : N.aggregateRate κ ρ =
          ∑ r ∈ Finset.univ with N.reaction r = ρ, κ.k r := by
        unfold aggregateRate
        simpa using (Finset.sum_filter
          (s := Finset.univ) (fun r : N.R => N.reaction r = ρ) (fun r => κ.k r)).symm
      rw [if_pos hy, hagg, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r hr
      have hrr : N.reaction r = ρ := (Finset.mem_filter.mp hr).2
      have hrsrc : (N.reaction r).source = y := by rw [hrr, hy]
      rw [if_pos hrsrc]
      simp [Network.reactionVector, hrr]
    · rw [if_neg hy]
      symm
      apply Finset.sum_eq_zero
      intro r hr
      have hrr : N.reaction r = ρ := (Finset.mem_filter.mp hr).2
      have hrsrc : (N.reaction r).source ≠ y := by
        intro h
        apply hy
        simpa [hrr] using h
      simp [hrsrc]
  calc
    (∑ ρ ∈ N.distinctReactions,
      if ρ.source = y then N.aggregateRate κ ρ * ρ.vector s else 0) =
      ∑ ρ ∈ N.distinctReactions,
        ∑ r ∈ Finset.univ with N.reaction r = ρ,
          (if (N.reaction r).source = y then κ.k r * N.reactionVector r s else 0) := by
        apply Finset.sum_congr rfl
        intro ρ hρ
        exact hfiber ρ hρ
    _ = ∑ r : N.R, if (N.reaction r).source = y then
        κ.k r * N.reactionVector r s else 0 := by
      exact Finset.sum_fiberwise_of_maps_to
        (s := Finset.univ) (t := N.distinctReactions)
        (g := fun r : N.R => N.reaction r)
        (fun r _ => Finset.mem_image.mpr ⟨r, Finset.mem_univ r, rfl⟩)
        (fun r => if (N.reaction r).source = y then κ.k r * N.reactionVector r s else 0)

/-- **Parallel-channel aggregation preserves the complete mass-action vector field.** -/
theorem mergeParallel_dynamicallyEquivalent
    (N : Network S) (κ : N.RateConstants) :
    N.SourceCoefficientEquivalent N.mergeParallel κ (N.mergedRateConstants κ) := by
  intro y
  exact (N.mergeParallel_sourceCoefficient κ y).symm

/-- Consequently the merged realization has exactly the same steady states. -/
theorem mergeParallel_steadyState_iff
    (N : Network S) (κ : N.RateConstants) (x : Concentration S) :
    N.IsMassActionSteadyState κ x ↔
      N.mergeParallel.IsMassActionSteadyState (N.mergedRateConstants κ) x :=
  (steadyState_iff_of_sourceCoefficientEquivalent
    (N.mergeParallel_dynamicallyEquivalent κ)) x

/-- Merging parallel reactions leaves the stoichiometric subspace unchanged. -/
theorem mergeParallel_stoichSubspace (N : Network S) :
    N.mergeParallel.stoichSubspace = N.stoichSubspace := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro v hv
    rcases hv with ⟨ρ, rfl⟩
    rcases Finset.mem_image.mp ρ.2 with ⟨r, _, hr⟩
    have hvec : N.mergeParallel.reactionVector ρ = N.reactionVector r := by
      funext s
      simp [Network.reactionVector, mergeParallel, hr]
    rw [hvec]
    exact N.reactionVector_mem_stoichSubspace r
  · apply Submodule.span_le.mpr
    intro v hv
    rcases hv with ⟨r, rfl⟩
    have hm : N.reaction r ∈ N.distinctReactions :=
      Finset.mem_image.mpr ⟨r, Finset.mem_univ r, rfl⟩
    exact Submodule.subset_span ⟨⟨N.reaction r, hm⟩, rfl⟩

/-- Therefore parallel aggregation preserves stoichiometric rank. -/
theorem mergeParallel_stoichRank (N : Network S) :
    N.mergeParallel.stoichRank = N.stoichRank := by
  unfold Network.stoichRank
  rw [N.mergeParallel_stoichSubspace]

end Network
end CRNT
