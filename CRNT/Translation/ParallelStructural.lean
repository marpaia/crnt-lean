import CRNT.Translation.ParallelAggregation
import CRNT.Graph.WeakReversibility
import CRNT.Graph.Reversibility
import CRNT.Deficiency.DeficiencyOne
import CRNT.Equilibria.DetailedBalanced

/-!
# Structural invariants under parallel-channel aggregation

Merging duplicate reaction channels changes only reaction-index multiplicity.  It
preserves the reaction graph on complexes, linkage structure, weak reversibility,
reversibility, stoichiometric rank, and deficiency.  Aggregate detailed balance is
also invariant after summing rates over equal directed edges.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Complex sets are unchanged by merging parallel channels. -/
theorem mergeParallel_complexes (N : Network S) :
    N.mergeParallel.complexes = N.complexes := by
  ext y
  simp only [Network.complexes, mergeParallel]
  constructor
  · intro hy
    rcases Finset.mem_union.mp hy with hy | hy
    · rcases Finset.mem_image.mp hy with ⟨ρ, _, hρ⟩
      rcases Finset.mem_image.mp ρ.2 with ⟨r, _, hr⟩
      apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      exact ⟨r, Finset.mem_univ r, by simpa [hr] using hρ⟩
    · rcases Finset.mem_image.mp hy with ⟨ρ, _, hρ⟩
      rcases Finset.mem_image.mp ρ.2 with ⟨r, _, hr⟩
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      exact ⟨r, Finset.mem_univ r, by simpa [hr] using hρ⟩
  · intro hy
    rcases Finset.mem_union.mp hy with hy | hy
    · rcases Finset.mem_image.mp hy with ⟨r, _, hr⟩
      have hm : N.reaction r ∈ N.distinctReactions :=
        Finset.mem_image.mpr ⟨r, Finset.mem_univ r, rfl⟩
      apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      exact ⟨⟨N.reaction r, hm⟩, Finset.mem_univ _, by simpa [hr]⟩
    · rcases Finset.mem_image.mp hy with ⟨r, _, hr⟩
      have hm : N.reaction r ∈ N.distinctReactions :=
        Finset.mem_image.mpr ⟨r, Finset.mem_univ r, rfl⟩
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      exact ⟨⟨N.reaction r, hm⟩, Finset.mem_univ _, by simpa [hr]⟩

@[simp] theorem mergeParallel_numComplexes (N : Network S) :
    N.mergeParallel.numComplexes = N.numComplexes := by
  simp [Network.numComplexes, N.mergeParallel_complexes]

/-- Directed adjacency of complexes is unchanged. -/
theorem mergeParallel_directlyReacts_iff (N : Network S) (y z : Complex S) :
    N.mergeParallel.DirectlyReacts y z ↔ N.DirectlyReacts y z := by
  constructor
  · rintro ⟨ρ, hs, ht⟩
    rcases Finset.mem_image.mp ρ.2 with ⟨r, _, hr⟩
    exact ⟨r, by simpa [mergeParallel, hr] using hs,
      by simpa [mergeParallel, hr] using ht⟩
  · rintro ⟨r, hs, ht⟩
    have hm : N.reaction r ∈ N.distinctReactions :=
      Finset.mem_image.mpr ⟨r, Finset.mem_univ r, rfl⟩
    exact ⟨⟨N.reaction r, hm⟩, by simpa [mergeParallel] using hs,
      by simpa [mergeParallel] using ht⟩

/-- Reachability is unchanged. -/
theorem mergeParallel_reaches_iff (N : Network S) (y z : Complex S) :
    N.mergeParallel.Reaches y z ↔ N.Reaches y z := by
  constructor
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail hxy hyz ih =>
      exact Relation.ReflTransGen.tail ih ((N.mergeParallel_directlyReacts_iff _ _).1 hyz)
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail hxy hyz ih =>
      exact Relation.ReflTransGen.tail ih ((N.mergeParallel_directlyReacts_iff _ _).2 hyz)

/-- Undirected linkage is unchanged by merging parallel channels. -/
theorem mergeParallel_linked_iff (N : Network S) (y z : Complex S) :
    N.mergeParallel.Linked y z ↔ N.Linked y z := by
  constructor
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail hxy hyz ih =>
      apply Relation.ReflTransGen.tail ih
      rcases hyz with hyz | hyz
      · exact Or.inl ((N.mergeParallel_directlyReacts_iff _ _).1 hyz)
      · exact Or.inr ((N.mergeParallel_directlyReacts_iff _ _).1 hyz)
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail hxy hyz ih =>
      apply Relation.ReflTransGen.tail ih
      rcases hyz with hyz | hyz
      · exact Or.inl ((N.mergeParallel_directlyReacts_iff _ _).2 hyz)
      · exact Or.inr ((N.mergeParallel_directlyReacts_iff _ _).2 hyz)

/-- Linkage-class count is unchanged. -/
theorem mergeParallel_numLinkageClasses (N : Network S) :
    N.mergeParallel.numLinkageClasses = N.numLinkageClasses := by
  unfold Network.numLinkageClasses
  let e : {c : Complex S // c ∈ N.mergeParallel.complexes} ≃
      {c : Complex S // c ∈ N.complexes} :=
    { toFun := fun c => ⟨c.1, by simpa [N.mergeParallel_complexes] using c.2⟩
      invFun := fun c => ⟨c.1, by simpa [N.mergeParallel_complexes] using c.2⟩
      left_inv := by intro c; apply Subtype.ext; rfl
      right_inv := by intro c; apply Subtype.ext; rfl }
  apply Nat.card_congr
  exact Quotient.congr e (by
    intro a b
    change N.mergeParallel.Linked a.1 b.1 ↔ N.Linked (e a).1 (e b).1
    simpa [e] using N.mergeParallel_linked_iff a.1 b.1)

/-- Deficiency is unchanged by aggregation of parallel channels. -/
theorem mergeParallel_deficiency (N : Network S) :
    N.mergeParallel.deficiency = N.deficiency := by
  have hm := N.mergeParallel.numComplexes_eq_add
  have hn := N.numComplexes_eq_add
  rw [N.mergeParallel_numComplexes, N.mergeParallel_numLinkageClasses,
    N.mergeParallel_stoichRank] at hm
  omega

/-- Weak reversibility is invariant. -/
theorem mergeParallel_weaklyReversible_iff (N : Network S) :
    N.mergeParallel.WeaklyReversible ↔ N.WeaklyReversible := by
  constructor
  · intro hm r
    have hmem : N.reaction r ∈ N.distinctReactions :=
      Finset.mem_image.mpr ⟨r, Finset.mem_univ r, rfl⟩
    have h := hm ⟨N.reaction r, hmem⟩
    exact (N.mergeParallel_reaches_iff _ _).1 (by simpa [mergeParallel] using h)
  · intro hn ρ
    rcases Finset.mem_image.mp ρ.2 with ⟨r, _, hr⟩
    have h := hn r
    apply (N.mergeParallel_reaches_iff _ _).2
    simpa [mergeParallel, hr] using h

/-- Reversibility is invariant at the level of directed reaction existence. -/
theorem mergeParallel_reversible_iff (N : Network S) :
    N.mergeParallel.Reversible ↔ N.Reversible := by
  rw [N.mergeParallel.reversible_iff_directlyReacts_symm,
      N.reversible_iff_directlyReacts_symm]
  constructor
  · intro hm c d hcd
    have hmd : N.mergeParallel.DirectlyReacts c d :=
      (N.mergeParallel_directlyReacts_iff c d).2 hcd
    exact (N.mergeParallel_directlyReacts_iff d c).1 (hm hmd)
  · intro hn c d hcd
    have hnd : N.DirectlyReacts c d :=
      (N.mergeParallel_directlyReacts_iff c d).1 hcd
    exact (N.mergeParallel_directlyReacts_iff d c).2 (hn hnd)

/-- Deficiency zero is invariant. -/
theorem mergeParallel_deficiencyZero_iff (N : Network S) :
    N.mergeParallel.DeficiencyZero ↔ N.DeficiencyZero := by
  rw [N.mergeParallel.deficiencyZero_iff_deficiency_eq_zero,
    N.deficiencyZero_iff_deficiency_eq_zero, N.mergeParallel_deficiency]

/-- Deficiency one is invariant. -/
theorem mergeParallel_deficiencyOne_iff (N : Network S) :
    N.mergeParallel.DeficiencyOne ↔ N.DeficiencyOne := by
  rw [N.mergeParallel.deficiencyOne_iff_deficiency_eq_one,
    N.deficiencyOne_iff_deficiency_eq_one, N.mergeParallel_deficiency]

/-- Aggregate flux from one complex to another is preserved when parallel channels
are merged and their rate constants summed. -/
theorem mergeParallel_aggregateComplexFlux
    (N : Network S) (κ : N.RateConstants) (x : Concentration S)
    (y z : Complex S) :
    N.pairFlux κ x y z =
      N.mergeParallel.pairFlux (N.mergedRateConstants κ) x y z := by
  classical
  unfold pairFlux
  change (∑ r : N.R,
      if (N.reaction r).source = y ∧ (N.reaction r).target = z then
        κ.k r * (N.reaction r).source.massActionMonomial x else 0) =
    ∑ ρ : {ρ : Reaction S // ρ ∈ N.distinctReactions},
      if ρ.1.source = y ∧ ρ.1.target = z then
        N.aggregateRate κ ρ.1 * ρ.1.source.massActionMonomial x else 0
  have hsubtype :
      (∑ ρ : {ρ : Reaction S // ρ ∈ N.distinctReactions},
        if ρ.1.source = y ∧ ρ.1.target = z then
          N.aggregateRate κ ρ.1 * ρ.1.source.massActionMonomial x else 0) =
      ∑ ρ ∈ N.distinctReactions,
        if ρ.source = y ∧ ρ.target = z then
          N.aggregateRate κ ρ * ρ.source.massActionMonomial x else 0 := by
    symm
    exact Finset.sum_subtype N.distinctReactions (fun ρ => Iff.rfl)
      (fun ρ => if ρ.source = y ∧ ρ.target = z then
        N.aggregateRate κ ρ * ρ.source.massActionMonomial x else 0)
  rw [hsubtype]
  symm
  have hfiber : ∀ ρ ∈ N.distinctReactions,
      (if ρ.source = y ∧ ρ.target = z then
          N.aggregateRate κ ρ * ρ.source.massActionMonomial x else 0) =
      ∑ r ∈ Finset.univ with N.reaction r = ρ,
        (if (N.reaction r).source = y ∧ (N.reaction r).target = z then
          κ.k r * (N.reaction r).source.massActionMonomial x else 0) := by
    intro ρ hρ
    by_cases hp : ρ.source = y ∧ ρ.target = z
    · have hagg : N.aggregateRate κ ρ =
          ∑ r ∈ Finset.univ with N.reaction r = ρ, κ.k r := by
        unfold aggregateRate
        simpa using (Finset.sum_filter
          (s := Finset.univ) (fun r : N.R => N.reaction r = ρ) (fun r => κ.k r)).symm
      rw [if_pos hp, hagg, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r hr
      have hrr : N.reaction r = ρ := (Finset.mem_filter.mp hr).2
      have hrp : (N.reaction r).source = y ∧ (N.reaction r).target = z := by
        simpa [hrr] using hp
      rw [if_pos hrp]
      simp [hrr]
    · rw [if_neg hp]
      symm
      apply Finset.sum_eq_zero
      intro r hr
      have hrr : N.reaction r = ρ := (Finset.mem_filter.mp hr).2
      have hrp : ¬ ((N.reaction r).source = y ∧ (N.reaction r).target = z) := by
        intro h
        apply hp
        simpa [hrr] using h
      simp [hrp]
  calc
    (∑ ρ ∈ N.distinctReactions,
      if ρ.source = y ∧ ρ.target = z then
        N.aggregateRate κ ρ * ρ.source.massActionMonomial x else 0) =
      ∑ ρ ∈ N.distinctReactions,
        ∑ r ∈ Finset.univ with N.reaction r = ρ,
          (if (N.reaction r).source = y ∧ (N.reaction r).target = z then
            κ.k r * (N.reaction r).source.massActionMonomial x else 0) := by
        apply Finset.sum_congr rfl
        intro ρ hρ
        exact hfiber ρ hρ
    _ = ∑ r : N.R,
        if (N.reaction r).source = y ∧ (N.reaction r).target = z then
          κ.k r * (N.reaction r).source.massActionMonomial x else 0 := by
      exact Finset.sum_fiberwise_of_maps_to
        (s := Finset.univ) (t := N.distinctReactions)
        (g := fun r : N.R => N.reaction r)
        (fun r _ => Finset.mem_image.mpr ⟨r, Finset.mem_univ r, rfl⟩)
        (fun r => if (N.reaction r).source = y ∧ (N.reaction r).target = z then
          κ.k r * (N.reaction r).source.massActionMonomial x else 0)

/-- Hence aggregate detailed balance is invariant under parallel aggregation. -/
theorem mergeParallel_detailedBalanced_iff
    (N : Network S) (κ : N.RateConstants) (x : Concentration S) :
    N.IsDetailedBalanced κ x ↔
      N.mergeParallel.IsDetailedBalanced (N.mergedRateConstants κ) x := by
  constructor
  · intro h c hc d hd
    have hcN : c ∈ N.complexes := by simpa [N.mergeParallel_complexes] using hc
    have hdN : d ∈ N.complexes := by simpa [N.mergeParallel_complexes] using hd
    rw [← N.mergeParallel_aggregateComplexFlux κ x c d,
        ← N.mergeParallel_aggregateComplexFlux κ x d c]
    exact h c hcN d hdN
  · intro h c hc d hd
    have hcM : c ∈ N.mergeParallel.complexes := by simpa [N.mergeParallel_complexes] using hc
    have hdM : d ∈ N.mergeParallel.complexes := by simpa [N.mergeParallel_complexes] using hd
    rw [N.mergeParallel_aggregateComplexFlux κ x c d,
        N.mergeParallel_aggregateComplexFlux κ x d c]
    exact h c hcM d hdM

end Network
end CRNT
