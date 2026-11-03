import CRNT.Geometry.EndotacticGlobal

/-!
# Projection of a reaction network to a species subset

For a finite species set `P`, `speciesProjection N P` keeps every reaction channel of `N` but
restricts each source and target complex to the coordinates in `P`.  Parallel reactions and
reactions that become self-reactions after projection are intentionally retained; this makes the
projection functorial and avoids quotient bookkeeping.

The main result is the structural ingredient used in the strongly-endotactic permanence proof:
standard strong endotacticity is preserved by projection to an arbitrary species subset.
-/

open scoped BigOperators

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Restrict a complex to a finite species subset. -/
def projectComplex (P : Finset S) (y : Complex S) : Complex {s // s ∈ P} :=
  fun s => y s.1

/-- Restrict a reaction to a finite species subset. -/
def projectReaction (P : Finset S) (r : Reaction S) : Reaction {s // s ∈ P} :=
  ⟨projectComplex P r.source, projectComplex P r.target⟩

/-- Project a network onto a finite subset of its species, retaining the original reaction-index
set. -/
def speciesProjection (N : Network S) (P : Finset S) : Network {s // s ∈ P} where
  R := N.R
  decEqR := N.decEqR
  fintypeR := N.fintypeR
  reaction := fun r => projectReaction P (N.reaction r)

@[simp] theorem speciesProjection_reaction (N : Network S) (P : Finset S) (r : N.R) :
    (N.speciesProjection P).reaction r = projectReaction P (N.reaction r) := rfl

@[simp] theorem projectComplex_apply (P : Finset S) (y : Complex S) (s : {s // s ∈ P}) :
    projectComplex P y s = y s.1 := rfl

@[simp] theorem speciesProjection_source_apply (N : Network S) (P : Finset S) (r : N.R)
    (s : {s // s ∈ P}) :
    ((N.speciesProjection P).reaction r).source s = (N.reaction r).source s.1 := rfl

@[simp] theorem speciesProjection_target_apply (N : Network S) (P : Finset S) (r : N.R)
    (s : {s // s ∈ P}) :
    ((N.speciesProjection P).reaction r).target s = (N.reaction r).target s.1 := rfl

@[simp] theorem speciesProjection_reactionVector_apply (N : Network S) (P : Finset S)
    (r : N.R) (s : {s // s ∈ P}) :
    (N.speciesProjection P).reactionVector r s = N.reactionVector r s.1 := by
  simp [reactionVector_apply, speciesProjection, projectReaction]

/-- Extend a linear direction on the projected species set by zero on the omitted species. -/
def extendProjectedWeight (P : Finset S) (w : {s // s ∈ P} → ℝ) : S → ℝ :=
  fun s => if h : s ∈ P then w ⟨s, h⟩ else 0

@[simp] theorem extendProjectedWeight_apply_mem (P : Finset S) (w : {s // s ∈ P} → ℝ)
    (s : {s // s ∈ P}) : extendProjectedWeight P w s.1 = w s := by
  simp [extendProjectedWeight, s.2]

@[simp] theorem extendProjectedWeight_apply_not_mem (P : Finset S)
    (w : {s // s ∈ P} → ℝ) {s : S} (hs : s ∉ P) :
    extendProjectedWeight P w s = 0 := by
  simp [extendProjectedWeight, hs]

/-- Summing a zero-extended projected direction over the ambient species is the same as summing
on the projected species subtype. -/
theorem sum_extendProjectedWeight_mul (P : Finset S) (w : {s // s ∈ P} → ℝ)
    (v : S → ℝ) :
    (∑ s : S, extendProjectedWeight P w s * v s) =
      ∑ s : {s // s ∈ P}, w s * v s.1 := by
  -- Restrict the ambient sum to `P` (the extension vanishes off `P`), then convert the
  -- `Finset` sum to a subtype sum.  Going through `Fintype.sum_subtype_add_sum_subtype`
  -- instead produces a second, non-unifying `Fintype` instance on the subtype.
  have h1 : (∑ s ∈ P, extendProjectedWeight P w s * v s)
      = ∑ s : S, extendProjectedWeight P w s * v s := by
    refine Finset.sum_subset (Finset.subset_univ P) ?_
    intro s _ hsP
    simp [extendProjectedWeight, hsP]
  rw [← h1, Finset.sum_subtype P (fun _ => Iff.rfl)
    (fun s => extendProjectedWeight P w s * v s)]
  refine Finset.sum_congr rfl ?_
  intro s _
  simp [extendProjectedWeight, s.2]

/-- Projected source potentials are ambient source potentials for the zero-extended direction. -/
theorem speciesProjection_wValue (N : Network S) (P : Finset S)
    (w : {s // s ∈ P} → ℝ) (r : N.R) :
    (N.speciesProjection P).wValue w r = N.wValue (extendProjectedWeight P w) r := by
  change (∑ s : {s // s ∈ P}, w s * exponentVector (N.reaction r).source s) =
    ∑ s : S, extendProjectedWeight P w s * exponentVector (N.reaction r).source s
  symm
  exact sum_extendProjectedWeight_mul P w (exponentVector (N.reaction r).source)

/-- Projected reaction rates are ambient reaction rates for the zero-extended direction. -/
theorem speciesProjection_wRate (N : Network S) (P : Finset S)
    (w : {s // s ∈ P} → ℝ) (r : N.R) :
    (N.speciesProjection P).wRate w r = N.wRate (extendProjectedWeight P w) r := by
  change (∑ s : {s // s ∈ P}, w s * N.reactionVector r s.1) =
    ∑ s : S, extendProjectedWeight P w s * N.reactionVector r s
  symm
  exact sum_extendProjectedWeight_mul P w (N.reactionVector r)

/-- Maximal-source status is preserved exactly under zero extension of a projected direction. -/
theorem speciesProjection_isMaxSource_iff (N : Network S) (P : Finset S)
    (w : {s // s ∈ P} → ℝ) (r : N.R) :
    (N.speciesProjection P).IsMaxSource w r ↔ N.IsMaxSource (extendProjectedWeight P w) r := by
  simp only [IsMaxSource, speciesProjection_wValue]
  constructor
  · intro h r'
    have h' := h r'
    rw [speciesProjection_wValue N P w r'] at h'
    exact h'
  · intro h r'
    rw [speciesProjection_wValue N P w r']
    exact h r'

/-- Stoichiometric activity of a projected direction is the same as activity of its zero extension. -/
theorem speciesProjection_stoichActive_iff (N : Network S) (P : Finset S)
    (w : {s // s ∈ P} → ℝ) :
    (N.speciesProjection P).StoichActiveDirection w ↔
      N.StoichActiveDirection (extendProjectedWeight P w) := by
  simp only [StoichActiveDirection, speciesProjection_wRate]
  constructor
  · rintro ⟨r, hr⟩
    have hr' := hr
    rw [speciesProjection_wRate N P w r] at hr'
    exact ⟨r, hr'⟩
  · rintro ⟨r, hr⟩
    refine ⟨r, ?_⟩
    rw [speciesProjection_wRate N P w r]
    exact hr

/-- **Species projection preserves endotacticity.** -/
theorem Endotactic.speciesProjection {N : Network S} (h : N.Endotactic) (P : Finset S) :
    (N.speciesProjection P).Endotactic := by
  intro w r hmax
  have hmax' := (N.speciesProjection_isMaxSource_iff P w r).mp hmax
  have hrate := h (extendProjectedWeight P w) r hmax'
  rw [speciesProjection_wRate N P w r]
  exact hrate

/-- **Species projection preserves standard strong endotacticity.**

This is the structural projection lemma used in the boundary part of the permanence proof. -/
theorem StronglyEndotacticStd.speciesProjection {N : Network S}
    (h : N.StronglyEndotacticStd) (P : Finset S) :
    (N.speciesProjection P).StronglyEndotacticStd := by
  refine ⟨h.1.speciesProjection P, ?_⟩
  intro w hactive
  have hactive' : N.StoichActiveDirection (extendProjectedWeight P w) :=
    (N.speciesProjection_stoichActive_iff P w).mp hactive
  obtain ⟨r, hmax, hneg⟩ := h.2 (extendProjectedWeight P w) hactive'
  refine ⟨r, (N.speciesProjection_isMaxSource_iff P w r).mpr hmax, ?_⟩
  simpa only [speciesProjection_wRate] using hneg

end Network
end CRNT
