import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Sorting a cycle by source value makes its base vertex minimal

This supplies the `cmin` half of the `NetworkCycleDecomposition` repair discussed in
`CRNT/Dynamics/ToricCycleOrderLimits.lean` and `docs/persistence-gac.md` item 3.

Setting.  A closed walk of reaction vectors contributes `∑ i, a i • d i` to the velocity, and that
sum depends only on the multiset of pairs `(a i, d i)` — not on the order the steps are taken in.
So the steps may be *reordered* freely, and reordering by increasing coefficient satisfies the
`mono` field of `NetworkCycleDecomposition`.  What was missing is that the reordered walk's base
vertex is still minimal for the relevant linear functional, since after reordering the vertices are
partial sums of reaction vectors in coefficient order rather than source complexes.

For mass action with a single direction `z`, the coefficient of a reaction is an increasing function
of `⟪z, source⟫`, so sorting by coefficient is sorting by source value.  Writing `s i` for the
source value of the `i`-th complex of a graph cycle, the step values are `s (i+1) - s i` (cyclically),
and the partial sum over the `k` lowest-source steps is
`∑_{j ∈ L.image (·+1)} s j - ∑_{j ∈ L} s j`, where `L` is the set of those `k` indices.  Both index
sets have `k` elements and `L` carries the `k` smallest values of `s`, so the first sum dominates.
Hence every partial sum is nonnegative: the sorted walk never dips below its base vertex in the `z`
direction, which is exactly `CMinimal` for `C` the ray through `z`.

`cyclicStep_sum_nonneg` is that statement; `sum_le_sum_of_downwardClosed` is the extremal fact it
rests on.  Both are order-theoretic and carry no chemistry.

Scope.  This handles one direction `z` at a time.  `CMinimal C u` quantifies over all `z ∈ C`, and a
single reordering cannot sort for several functionals at once, so a cone `C` of dimension above one
still needs a separate argument.
-/

open scoped InnerProductSpace
open Finset

namespace CRNT

/-- **A downward-closed set carries the smallest sum among sets of its size.**  If every element of
`L` has `s`-value at most that of every element outside `L`, then `L` minimises `∑ s` over all
finsets of the same cardinality. -/
theorem sum_le_sum_of_downwardClosed {α : Type*} [DecidableEq α]
    (s : α → ℝ) {L M : Finset α} (hcard : L.card = M.card)
    (hdc : ∀ i ∈ L, ∀ j, j ∉ L → s i ≤ s j) :
    ∑ i ∈ L, s i ≤ ∑ i ∈ M, s i := by
  classical
  have hL : ∑ i ∈ L \ M, s i + ∑ i ∈ L ∩ M, s i = ∑ i ∈ L, s i := by
    rw [← Finset.sdiff_inter_self_left L M]
    exact Finset.sum_sdiff Finset.inter_subset_left
  have hM : ∑ i ∈ M \ L, s i + ∑ i ∈ L ∩ M, s i = ∑ i ∈ M, s i := by
    rw [Finset.inter_comm L M, ← Finset.sdiff_inter_self_left M L]
    exact Finset.sum_sdiff Finset.inter_subset_left
  have hcards : (L \ M).card = (M \ L).card := by
    have h1 : (L \ M).card + (L ∩ M).card = L.card :=
      Finset.card_sdiff_add_card_inter L M
    have h2 : (M \ L).card + (M ∩ L).card = M.card :=
      Finset.card_sdiff_add_card_inter M L
    rw [Finset.inter_comm M L] at h2
    omega
  have key : ∑ i ∈ L \ M, s i ≤ ∑ i ∈ M \ L, s i := by
    rcases Finset.eq_empty_or_nonempty (L \ M) with hempty | hne
    · have hMempty : (M \ L) = ∅ := by
        rw [← Finset.card_eq_zero, ← hcards, hempty, Finset.card_empty]
      rw [hempty, hMempty]
    · obtain ⟨i₀, hi₀mem, hi₀max⟩ := Finset.exists_max_image (L \ M) s hne
      have hiL : i₀ ∈ L := (Finset.mem_sdiff.mp hi₀mem).1
      have hupper : ∑ i ∈ L \ M, s i ≤ (L \ M).card • s i₀ :=
        Finset.sum_le_card_nsmul _ _ _ (fun i hi => hi₀max i hi)
      have hlower : (M \ L).card • s i₀ ≤ ∑ i ∈ M \ L, s i := by
        refine Finset.card_nsmul_le_sum _ _ _ ?_
        intro j hj
        exact hdc i₀ hiL j (Finset.mem_sdiff.mp hj).2
      rw [hcards] at hupper
      exact le_trans hupper hlower
  linarith [hL, hM, key]

/-- **Sorting a cycle by source value keeps the base vertex minimal.**  For a cyclic value function
`s` on `Fin n` and a set `L` of indices carrying the smallest values, the total of the cyclic steps
`s (i+1) - s i` taken over `L` is nonnegative.

Applied with `L` the `k` lowest-coefficient steps of a reordered closed walk, this says the walk's
`k`-th partial sum is at least its base value — i.e. the sorted walk's base vertex is minimal in the
`s` direction. -/
theorem cyclicStep_sum_nonneg {n : ℕ} [NeZero n] (s : Fin n → ℝ) {L : Finset (Fin n)}
    (hdc : ∀ i ∈ L, ∀ j, j ∉ L → s i ≤ s j) :
    0 ≤ ∑ i ∈ L, (s (i + 1) - s i) := by
  classical
  have hinj : Function.Injective (fun i : Fin n => i + 1) := add_left_injective 1
  have himg : ∑ i ∈ L, s (i + 1) = ∑ j ∈ L.image (fun i : Fin n => i + 1), s j := by
    rw [Finset.sum_image (fun a _ b _ h => hinj h)]
  have hcard : L.card = (L.image (fun i : Fin n => i + 1)).card :=
    (Finset.card_image_of_injective L hinj).symm
  have hle := sum_le_sum_of_downwardClosed s hcard hdc
  rw [Finset.sum_sub_distrib, himg]
  exact sub_nonneg.mpr hle



section SortedPrefix

/-- The index set of the `k` smallest entries of `a`, as the `Tuple.sort` image of the first `k`
positions. -/
noncomputable def sortedPrefix {n : ℕ} (a : Fin n → ℝ) (k : ℕ) : Finset (Fin n) :=
  Finset.image (Tuple.sort a) (Finset.univ.filter fun p : Fin n => (p : ℕ) < k)

/-- **The sorted prefixes are exactly the downward-closed sets.**  Every entry inside
`sortedPrefix a k` has `a`-value at most every entry outside it.  This is the hypothesis
`cyclicStep_sum_nonneg` and `inner_cyclicStep_sum_nonneg_of_orderRefines` ask for, so the two
lemmas apply to the prefixes of the coefficient sort with no further input. -/
theorem downwardClosed_sortedPrefix {n : ℕ} (a : Fin n → ℝ) (k : ℕ) :
    ∀ i ∈ sortedPrefix a k, ∀ j, j ∉ sortedPrefix a k → a i ≤ a j := by
  classical
  intro i hi j hj
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hi
  have hpk : (p : ℕ) < k := (Finset.mem_filter.mp hp).2
  -- `j` is the image of some position at or beyond `k`
  set q : Fin n := (Tuple.sort a).symm j with hq
  have hjq : j = Tuple.sort a q := by simp [hq]
  have hqk : ¬ ((q : ℕ) < k) := by
    intro hlt
    exact hj (Finset.mem_image.mpr ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ q, hlt⟩,
      hjq.symm⟩)
  have hpq : p ≤ q := by
    have : (p : ℕ) ≤ (q : ℕ) := by omega
    exact this
  have hmono := Tuple.monotone_sort a hpq
  rw [hjq]
  exact hmono

end SortedPrefix

section Chamber

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The chamber condition.**  The coefficient order refines the `⟪z, ·⟫` order of the vertices,
simultaneously for every `z ∈ C`.  For mass action on a cone `C` lying inside a single chamber of
the arrangement `{z : ⟪z, y i - y j⟫ = 0}`, the monomial ordering is constant across `C`, so this
holds; it is exactly what the toric fan of `Geometry/ToricFan.lean` is for. -/
def OrderRefines (C : Set E) {n : ℕ} (y : Fin n → E) (a : Fin n → ℝ) : Prop :=
  ∀ z ∈ C, ∀ i j, a i ≤ a j → ⟪z, y i⟫_ℝ ≤ ⟪z, y j⟫_ℝ

/-- **Under the chamber condition the coefficient-sorted walk is `C`-minimal.**  If `L` collects the
lowest-coefficient steps, then the partial sum of the corresponding cyclic vertex differences pairs
nonnegatively with every `z ∈ C` — i.e. the sorted walk never dips below its base vertex in any
direction of `C`.

This is the higher-dimensional completion of `cyclicStep_sum_nonneg`, which handled a single
direction.  The extra input is `OrderRefines`: one permutation cannot sort for several functionals
at once, so `C` must be confined to a region where the vertex ordering does not change. -/
theorem inner_cyclicStep_sum_nonneg_of_orderRefines {C : Set E} {n : ℕ} [NeZero n]
    (y : Fin n → E) (a : Fin n → ℝ) (hrefine : OrderRefines C y a)
    {L : Finset (Fin n)} (hL : ∀ i ∈ L, ∀ j, j ∉ L → a i ≤ a j)
    {z : E} (hz : z ∈ C) :
    0 ≤ ⟪z, ∑ i ∈ L, (y (i + 1) - y i)⟫_ℝ := by
  classical
  have hdc : ∀ i ∈ L, ∀ j, j ∉ L → ⟪z, y i⟫_ℝ ≤ ⟪z, y j⟫_ℝ :=
    fun i hi j hj => hrefine z hz i j (hL i hi j hj)
  have h := cyclicStep_sum_nonneg (fun i => ⟪z, y i⟫_ℝ) hdc
  calc (0 : ℝ) ≤ ∑ i ∈ L, (⟪z, y (i + 1)⟫_ℝ - ⟪z, y i⟫_ℝ) := h
    _ = ⟪z, ∑ i ∈ L, (y (i + 1) - y i)⟫_ℝ := by
        rw [inner_sum]
        exact Finset.sum_congr rfl fun i _ => (inner_sub_right _ _ _).symm

end Chamber

end CRNT
