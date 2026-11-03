import CRNT.Persistence.FieldDecomposition
import CRNT.Graph.WeakReversibility
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Weakly reversible fields push along every valid normal

This is the weakly reversible counterpart of `dot_massActionField_nonneg`
(`CRNT/Persistence/FieldDecomposition.lean`), with the same validity hypothesis on the normal `a`
and with complex balance replaced by weak reversibility plus a lower bound on the slack `δ`:

`|R| · k_i ≤ exp δ · k_j` for all reactions `i, j`.

Write `φ c = ⟨a, c⟩` and `h c = ⟨c, log x⟩`.  The validity hypothesis says that `φ c' > φ c`
forces `h c ≥ h c' + δ`.  Then for every threshold `θ`, every complex outside the upper set
`U = {φ ≥ θ}` has a mass-action monomial at least `exp δ` times that of every complex in `U`.
If some reaction leaves `U`, weak reversibility gives a path back, hence a reaction entering
`U` from outside; its rate alone dominates the total rate of all reactions leaving `U`.  So
every upper cut of `φ` receives at least the flux it emits (`cutSum ≥ 0`), and the layer-cake
inequality `cut_pairing_nonneg` gives `⟨a, f(x)⟩ ≥ 0`.

This is the field condition of Craciun's toric differential inclusion argument
(arXiv:1501.02860, Theorem 3.1 and §8) in the form used by `exists_zsh`.

Nothing here is an axiom or a `sorry`.
-/

namespace CRNT
namespace Persistence

open Finset

/-- The net weight entering the upper set `{φ ≥ θ}` along edges `src i → tgt i`. -/
noncomputable def cutSum {α ι : Type*} [Fintype ι] (src tgt : ι → α) (u : ι → ℝ)
    (φ : α → ℝ) (θ : ℝ) : ℝ :=
  ∑ i, u i * ((if θ ≤ φ (tgt i) then 1 else 0) - (if θ ≤ φ (src i) then 1 else 0))

/-- **Layer-cake inequality.** If the potential `φ` takes finitely many values on the edge
endpoints and every upper cut receives nonnegative net weight, then the weighted potential
increase `∑ u i (φ (tgt i) - φ (src i))` is nonnegative. -/
theorem cut_pairing_nonneg {α ι : Type*} [Fintype ι] (src tgt : ι → α) (u : ι → ℝ) :
    ∀ (V : Finset ℝ) (φ : α → ℝ), (∀ i, φ (src i) ∈ V) → (∀ i, φ (tgt i) ∈ V) →
      (∀ θ, 0 ≤ cutSum src tgt u φ θ) →
      0 ≤ ∑ i, u i * (φ (tgt i) - φ (src i)) := by
  intro V
  induction V using Finset.induction_on_max with
  | empty =>
    intro φ hs _ _
    rcases isEmpty_or_nonempty ι with hι | ⟨⟨i⟩⟩
    · simp
    · exact absurd (hs i) (Finset.notMem_empty _)
  | insert a s hlt ih =>
    intro φ hs ht hcut
    rcases s.eq_empty_or_nonempty with hse | hsne
    · have hc : ∀ i, φ (src i) = a ∧ φ (tgt i) = a := fun i => by
        have h1 := hs i; have h2 := ht i
        simp [hse] at h1 h2; exact ⟨h1, h2⟩
      refine le_of_eq (Eq.symm (Finset.sum_eq_zero fun i _ => ?_))
      rw [(hc i).1, (hc i).2]; ring
    set b := s.max' hsne with hb
    have hbs : b ∈ s := s.max'_mem hsne
    have hba : b < a := hlt b hbs
    set φ' : α → ℝ := fun c => min (φ c) b with hφ'
    have hval : ∀ c, φ c ∈ insert a s → φ' c ∈ s := by
      intro c hc
      rcases Finset.mem_insert.mp hc with h | h
      · have : φ' c = b := by simp [hφ', h, hba.le]
        rw [this]; exact hbs
      · have : φ' c = φ c := by simp only [hφ']; exact min_eq_left (s.le_max' _ h)
        rw [this]; exact h
    have hdiff : ∀ c, φ c ∈ insert a s →
        φ c - φ' c = (a - b) * (if a ≤ φ c then 1 else 0) := by
      intro c hc
      rcases Finset.mem_insert.mp hc with h | h
      · simp [hφ', h, hba.le]
      · have hle : φ c ≤ b := s.le_max' _ h
        have hlt' : ¬ a ≤ φ c := not_le.mpr (lt_of_le_of_lt hle hba)
        simp [hφ', hle, hlt']
    have hcut' : ∀ θ, 0 ≤ cutSum src tgt u φ' θ := by
      intro θ
      by_cases hθ : θ ≤ b
      · have : cutSum src tgt u φ' θ = cutSum src tgt u φ θ := by
          unfold cutSum
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [hφ', le_min_iff, hθ, and_true]
        rw [this]; exact hcut θ
      · have : cutSum src tgt u φ' θ = 0 := by
          unfold cutSum
          refine Finset.sum_eq_zero fun i _ => ?_
          simp only [hφ', le_min_iff, hθ, and_false, ite_false, sub_self, mul_zero]
        rw [this]
    have hIH := ih φ' (fun i => hval _ (hs i)) (fun i => hval _ (ht i)) hcut'
    have hsplit : ∑ i, u i * (φ (tgt i) - φ (src i)) =
        ∑ i, u i * (φ' (tgt i) - φ' (src i)) + (a - b) * cutSum src tgt u φ a := by
      unfold cutSum
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h1 := hdiff _ (ht i); have h2 := hdiff _ (hs i)
      have e : φ (tgt i) - φ (src i) = (φ' (tgt i) - φ' (src i)) +
          ((φ (tgt i) - φ' (tgt i)) - (φ (src i) - φ' (src i))) := by ring
      rw [e, h1, h2]; ring
    rw [hsplit]
    have := hcut a
    have : 0 ≤ (a - b) * cutSum src tgt u φ a := mul_nonneg (by linarith) this
    linarith

/-- A path from outside a set to inside it has an edge from outside to inside. -/
theorem exists_crossing_of_reflTransGen {α : Type*} {r : α → α → Prop} (P : α → Prop)
    {c d : α} (h : Relation.ReflTransGen r c d) (hc : ¬ P c) (hd : P d) :
    ∃ c' d', r c' d' ∧ ¬ P c' ∧ P d' := by
  induction h with
  | refl => exact absurd hd hc
  | @tail b _ _ hbd ih =>
    by_cases hb : P b
    · exact ih hb
    · exact ⟨_, _, hbd, hb, hd⟩

end Persistence

namespace Network

open Finset Real CRNT.Persistence

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Weakly reversible field condition.** For a weakly reversible network, a positive state
`x`, and a normal `a` satisfying the validity condition of `exists_zsh` with slack `δ`, the
mass-action field has nonnegative component along `a`, provided `exp δ` dominates `|R|` times
every ratio of rate constants. -/
theorem dot_massActionField_nonneg_of_weaklyReversible (N : Network S) (κ : N.RateConstants)
    (hwr : N.WeaklyReversible) {x : Concentration S} (hx : x.Positive) (a : S → ℝ) (δ : ℝ)
    (hδ : ∀ i j : N.R, (Fintype.card N.R : ℝ) * κ.k i ≤ exp δ * κ.k j)
    (hvalid : ∀ c ∈ N.complexes, ∀ c' ∈ N.complexes,
      ∑ s, a s * ((c s : ℝ) - c' s) < 0 → δ ≤ ∑ s, ((c s : ℝ) - c' s) * log (x s)) :
    0 ≤ ∑ s, a s * N.massActionVectorField κ x s := by
  set φ : Complex S → ℝ := fun c => ∑ s, a s * (c s : ℝ) with hφ
  set src : N.R → Complex S := fun r => (N.reaction r).source with hsrc
  set tgt : N.R → Complex S := fun r => (N.reaction r).target with htgt
  set u : N.R → ℝ := fun r => N.massActionRate κ r x with hu
  have hu0 : ∀ r, 0 ≤ u r := fun r => N.massActionRate_nonneg κ r hx.nonnegative
  have hdot : ∑ s, a s * N.massActionVectorField κ x s =
      ∑ r, u r * (φ (tgt r) - φ (src r)) := by
    simp only [massActionVectorField_apply, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun r _ => ?_
    simp only [hu, hφ, hsrc, htgt, reactionVector_apply]
    rw [← sum_sub_distrib, mul_sum]
    exact sum_congr rfl fun s _ => by ring
  rw [hdot]
  refine cut_pairing_nonneg src tgt u
    ((univ : Finset N.R).image (φ ∘ src) ∪ (univ : Finset N.R).image (φ ∘ tgt)) φ
    (fun i => mem_union_left _ (mem_image_of_mem _ (mem_univ i)))
    (fun i => mem_union_right _ (mem_image_of_mem _ (mem_univ i))) ?_
  intro θ
  by_cases hex : ∃ i, θ ≤ φ (src i) ∧ ¬ θ ≤ φ (tgt i)
  · obtain ⟨i₀, hi₀s, hi₀t⟩ := hex
    -- a reaction entering the cut
    obtain ⟨c', d', ⟨j, hjs, hjt⟩, hc', hd'⟩ :=
      exists_crossing_of_reflTransGen (fun c => θ ≤ φ c) (hwr i₀) hi₀t hi₀s
    have hjs' : ¬ θ ≤ φ (src j) := by simp only [hsrc, hjs]; exact hc'
    have hjt' : θ ≤ φ (tgt j) := by simp only [htgt, hjt]; exact hd'
    set n : ℝ := (Fintype.card N.R : ℝ) with hn
    have hnpos : 0 < n := by
      rw [hn]; exact_mod_cast Fintype.card_pos_iff.mpr ⟨j⟩
    -- every reaction leaving from inside the cut is small
    have hsmall : ∀ i, θ ≤ φ (src i) → n * u i ≤ u j := by
      intro i hi
      have hlt : ∑ s, a s * (((src j) s : ℝ) - (src i) s) < 0 := by
        have : ∑ s, a s * (((src j) s : ℝ) - (src i) s) = φ (src j) - φ (src i) := by
          simp only [hφ, ← sum_sub_distrib]; exact sum_congr rfl fun s _ => by ring
        rw [this]; linarith [not_le.mp hjs']
      have hv := hvalid (src j) (N.source_mem_complexes j) (src i) (N.source_mem_complexes i) hlt
      have hm : exp δ * (src i).massActionMonomial x ≤ (src j).massActionMonomial x := by
        rw [massActionMonomial_eq_exp hx, massActionMonomial_eq_exp hx, ← exp_add]
        apply exp_le_exp.mpr
        have : ∑ s, ((src j s : ℝ) - src i s) * log (x s) =
            ∑ s, (src j s : ℝ) * log (x s) - ∑ s, (src i s : ℝ) * log (x s) := by
          rw [← sum_sub_distrib]; exact sum_congr rfl fun s _ => by ring
        linarith
      have hmi : 0 ≤ (src i).massActionMonomial x :=
        Complex.massActionMonomial_nonneg hx.nonnegative _
      have hk := hδ i j
      simp only [hu, massActionRate]
      calc n * (κ.k i * (N.reaction i).source.massActionMonomial x)
          = (n * κ.k i) * (src i).massActionMonomial x := by simp only [hsrc]; ring
        _ ≤ (exp δ * κ.k j) * (src i).massActionMonomial x :=
            mul_le_mul_of_nonneg_right hk hmi
        _ = κ.k j * (exp δ * (src i).massActionMonomial x) := by ring
        _ ≤ κ.k j * (src j).massActionMonomial x :=
            mul_le_mul_of_nonneg_left hm (κ.positive j).le
        _ = κ.k j * (N.reaction j).source.massActionMonomial x := by simp only [hsrc]
    -- termwise lower bound
    have hterm : ∀ i, (if i = j then u j else 0) - (if θ ≤ φ (src i) then u i else 0) ≤
        u i * ((if θ ≤ φ (tgt i) then 1 else 0) - (if θ ≤ φ (src i) then 1 else 0)) := by
      intro i
      by_cases hij : i = j
      · subst hij; simp [hjs', hjt']
      · simp only [hij, ite_false]
        have := hu0 i
        split_ifs <;> linarith
    have hsum := sum_le_sum fun i (_ : i ∈ (univ : Finset N.R)) => hterm i
    rw [sum_sub_distrib, sum_ite_eq' univ j, ite_cond_eq_true _ _ (eq_true (mem_univ j))] at hsum
    have hout : ∑ i, (if θ ≤ φ (src i) then u i else 0) ≤ u j := by
      have : ∀ i, (if θ ≤ φ (src i) then u i else 0) ≤ u j / n := by
        intro i
        split_ifs with h
        · rw [le_div_iff₀ hnpos]; linarith [hsmall i h]
        · exact div_nonneg (hu0 j) hnpos.le
      calc ∑ i, (if θ ≤ φ (src i) then u i else 0) ≤ ∑ _i : N.R, u j / n :=
            sum_le_sum fun i _ => this i
        _ = u j := by
          rw [sum_const, card_univ, nsmul_eq_mul, ← hn]; field_simp
    unfold cutSum
    linarith
  · push Not at hex
    unfold cutSum
    refine sum_nonneg fun i _ => ?_
    have := hu0 i
    by_cases h1 : θ ≤ φ (src i)
    · have h2 := hex i h1
      simp [h1, h2]
    · simp only [h1, ite_false, sub_zero]
      split_ifs <;> linarith

end Network
end CRNT
