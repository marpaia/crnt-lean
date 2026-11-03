import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.GroupTheory.Perm.Cycle.Factors
import Mathlib.Basic.Real.Basic

/-!
# Nonnegativity of a determinant from the structure of its negative cycles

This is the purely algebraic core of the Banaji--Craciun determinant argument for the
species--reaction-graph criterion.

Let `H` be a real square matrix with unit diagonal.  Write the Leibniz term of a permutation
`τ` as `permWeight H τ = sign τ * ∏ i, H (τ i) i`, so that `H.det = ∑ τ, permWeight H τ`.
Because the diagonal is one, the weight is multiplicative over disjoint permutations
(`permWeight_mul_of_disjoint`), hence the weight of `τ` is the product of the weights of its
cycle factors.

**Theorem (`det_nonneg_of_negCycles`).**  Suppose every cycle of negative weight has weight
exactly `-1`, and any two distinct cycles of negative weight are disjoint.  Then
`0 ≤ H.det`.

The proof is a sign-reversing involution: if some negative cycle `e` is disjoint from every
cycle factor of `τ` of nonnegative weight, toggling the least such `e` in or out of `τ` flips
the sign of the weight and does not change the set of admissible `e`.  The terms that survive
are those with no negative cycle factor, and these are nonnegative.

Nothing here is an axiom or a `sorry`.
-/

open Equiv Finset

namespace CRNT
namespace DetCycle

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Leibniz term of `H` at `τ` (Mathlib's convention `M (σ i) i`). -/
noncomputable def permWeight (H : Matrix ι ι ℝ) (τ : Perm ι) : ℝ :=
  ((Perm.sign τ : ℤ) : ℝ) * ∏ i, H (τ i) i

theorem det_eq_sum_permWeight (H : Matrix ι ι ℝ) : H.det = ∑ τ, permWeight H τ := by
  rw [Matrix.det_apply']
  rfl

theorem permWeight_one (H : Matrix ι ι ℝ) (hdiag : ∀ i, H i i = 1) :
    permWeight H 1 = 1 := by
  simp [permWeight, hdiag]

/-- Multiplicativity of the weight over disjoint permutations (unit diagonal). -/
theorem permWeight_mul_of_disjoint (H : Matrix ι ι ℝ) (hdiag : ∀ i, H i i = 1)
    {τ e : Perm ι} (hd : τ.Disjoint e) :
    permWeight H (τ * e) = permWeight H τ * permWeight H e := by
  have hpt : ∀ i, H ((τ * e) i) i = H (τ i) i * H (e i) i := by
    intro i
    by_cases hei : e i = i
    · simp [Perm.mul_apply, hei, hdiag]
    · have hτi : τ i = i := (hd i).resolve_right hei
      have hee : e (e i) ≠ e i := fun h => hei (e.injective h)
      have hτe : τ (e i) = e i := (hd (e i)).resolve_right hee
      simp [Perm.mul_apply, hτe, hτi, hdiag]
  unfold permWeight
  rw [Perm.sign_mul, Units.val_mul, Int.cast_mul]
  simp_rw [hpt]
  rw [Finset.prod_mul_distrib]
  ring

/-- If every cycle factor of `e`-complement is disjoint from `e`, so is the permutation. -/
theorem disjoint_of_forall_cycleFactors (τ e : Perm ι)
    (h : ∀ c ∈ τ.cycleFactorsFinset, c.Disjoint e) : τ.Disjoint e := by
  intro x
  by_cases hx : τ x = x
  · exact Or.inl hx
  · right
    have hmem : τ.cycleOf x ∈ τ.cycleFactorsFinset :=
      Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr (Perm.mem_support.mpr hx)
    rcases h _ hmem x with h1 | h1
    · rw [Perm.cycleOf_apply_self] at h1
      exact absurd h1 hx
    · exact h1

/-- Removing a cycle factor leaves a permutation disjoint from it. -/
theorem disjoint_mul_inv_of_mem_cycleFactors {τ e : Perm ι}
    (he : e ∈ τ.cycleFactorsFinset) : (τ * e⁻¹).Disjoint e := by
  intro x
  by_cases hex : e x = x
  · exact Or.inr hex
  · left
    have hx' : e⁻¹ x ∈ e.support := by
      rw [Perm.mem_support]
      intro h
      apply hex
      have h2 : x = e⁻¹ x := by simpa using h
      exact (Perm.inv_eq_iff_eq.mp h2.symm).symm
    have h1 : e (e⁻¹ x) = τ (e⁻¹ x) := (Perm.mem_cycleFactorsFinset_iff.mp he).2 _ hx'
    simp only [Perm.mul_apply]
    rw [← h1]
    simp

/-- A permutation all of whose cycle factors have nonnegative weight has nonnegative weight. -/
theorem permWeight_nonneg_of_cycleFactors (H : Matrix ι ι ℝ) (hdiag : ∀ i, H i i = 1)
    (τ : Perm ι) (h : ∀ c ∈ τ.cycleFactorsFinset, 0 ≤ permWeight H c) :
    0 ≤ permWeight H τ := by
  refine Perm.cycle_induction_on
    (P := fun τ : Perm ι => (∀ c ∈ τ.cycleFactorsFinset, 0 ≤ permWeight H c) →
      0 ≤ permWeight H τ) τ ?_ ?_ ?_ h
  · intro _
    rw [permWeight_one H hdiag]
    exact zero_le_one
  · intro σ hσ hP
    exact hP σ (by rw [hσ.cycleFactorsFinset_eq_singleton]; exact Finset.mem_singleton_self _)
  · intro σ τ hd _ hσ hτ hP
    rw [hd.cycleFactorsFinset_mul_eq_union] at hP
    rw [permWeight_mul_of_disjoint H hdiag hd]
    exact mul_nonneg (hσ fun c hc => hP c (Finset.mem_union_left _ hc))
      (hτ fun c hc => hP c (Finset.mem_union_right _ hc))

section Involution

open Classical

/-- Canonical choice of an element of a finite set of permutations. -/
noncomputable def pickPerm (s : Finset (Perm ι)) : Perm ι :=
  if h : s.Nonempty then
    (Fintype.equivFin (Perm ι)).symm ((s.image (Fintype.equivFin (Perm ι))).min' (h.image _))
  else 1

theorem pickPerm_mem {s : Finset (Perm ι)} (h : s.Nonempty) : pickPerm s ∈ s := by
  unfold pickPerm
  rw [dif_pos h]
  have hm := Finset.min'_mem (s.image (Fintype.equivFin (Perm ι))) (h.image _)
  obtain ⟨a, ha, hae⟩ := Finset.mem_image.mp hm
  rw [← hae]
  simpa using ha

/-- The negative cycles. -/
noncomputable def negCycles (H : Matrix ι ι ℝ) : Finset (Perm ι) :=
  Finset.univ.filter (fun c => c.IsCycle ∧ permWeight H c < 0)

/-- The negative cycles that may be toggled in `τ`: those disjoint from every cycle factor of
`τ` of nonnegative weight. -/
noncomputable def admissible (H : Matrix ι ι ℝ) (τ : Perm ι) : Finset (Perm ι) :=
  (negCycles H).filter
    (fun e => ∀ c ∈ τ.cycleFactorsFinset, 0 ≤ permWeight H c → c.Disjoint e)

/-- The toggle. -/
noncomputable def toggle (H : Matrix ι ι ℝ) (τ : Perm ι) : Perm ι :=
  if pickPerm (admissible H τ) ∈ τ.cycleFactorsFinset then
    τ * (pickPerm (admissible H τ))⁻¹
  else τ * pickPerm (admissible H τ)

theorem admissible_eq_of_cycleFactors {H : Matrix ι ι ℝ} {τ τ' : Perm ι}
    (h : ∀ c, 0 ≤ permWeight H c →
      (c ∈ τ.cycleFactorsFinset ↔ c ∈ τ'.cycleFactorsFinset)) :
    admissible H τ = admissible H τ' := by
  ext e
  simp only [admissible, Finset.mem_filter]
  constructor
  · rintro ⟨he, hall⟩
    exact ⟨he, fun c hc hw => hall c ((h c hw).mpr hc) hw⟩
  · rintro ⟨he, hall⟩
    exact ⟨he, fun c hc hw => hall c ((h c hw).mp hc) hw⟩

end Involution

/-- **Nonnegativity of the determinant from the negative cycles.** -/
theorem det_nonneg_of_negCycles (H : Matrix ι ι ℝ) (hdiag : ∀ i, H i i = 1)
    (hA : ∀ c : Perm ι, c.IsCycle → permWeight H c < 0 → permWeight H c = -1)
    (hB : ∀ c d : Perm ι, c.IsCycle → d.IsCycle → permWeight H c < 0 →
      permWeight H d < 0 → c ≠ d → c.Disjoint d) :
    0 ≤ H.det := by
  classical
  rw [det_eq_sum_permWeight]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun τ => (admissible H τ).Nonempty)]
  -- the toggled part cancels
  have key : ∀ τ : Perm ι, (admissible H τ).Nonempty →
      admissible H (toggle H τ) = admissible H τ ∧
      permWeight H τ + permWeight H (toggle H τ) = 0 ∧
      toggle H τ ≠ τ ∧ toggle H (toggle H τ) = τ := by
    intro τ hne
    set e := pickPerm (admissible H τ) with he_def
    have heA : e ∈ admissible H τ := pickPerm_mem hne
    have heA' := heA
    simp only [admissible, negCycles, Finset.mem_filter, Finset.mem_univ, true_and] at heA'
    obtain ⟨⟨hecyc, hew⟩, hedisj⟩ := heA'
    have hew1 : permWeight H e = -1 := hA e hecyc hew
    have hene : e ≠ 1 := hecyc.ne_one
    by_cases hmem : e ∈ τ.cycleFactorsFinset
    · -- removal
      have hT : toggle H τ = τ * e⁻¹ := by
        simp only [toggle, ← he_def, if_pos hmem]
      have hfac : (τ * e⁻¹).cycleFactorsFinset = τ.cycleFactorsFinset \ {e} :=
        Perm.cycleFactorsFinset_mul_inv_mem_eq_sdiff hmem
      have hadm : admissible H (τ * e⁻¹) = admissible H τ := by
        apply admissible_eq_of_cycleFactors
        intro c hc
        rw [hfac, Finset.mem_sdiff, Finset.mem_singleton]
        constructor
        · exact fun h => h.1
        · intro h
          refine ⟨h, ?_⟩
          rintro rfl
          linarith
      have hdisj : (τ * e⁻¹).Disjoint e := disjoint_mul_inv_of_mem_cycleFactors hmem
      have hw : permWeight H τ = permWeight H (τ * e⁻¹) * permWeight H e := by
        rw [← permWeight_mul_of_disjoint H hdiag hdisj]
        simp
      refine ⟨by rw [hT, hadm], ?_, ?_, ?_⟩
      · rw [hT, hw, hew1]; ring
      · rw [hT]
        intro h
        apply hene
        have : e⁻¹ = 1 := by
          have := congrArg (fun p => τ⁻¹ * p) h
          simpa [mul_assoc] using this
        simpa using congrArg (fun p => p⁻¹) this
      · rw [hT]
        have hpick : pickPerm (admissible H (τ * e⁻¹)) = e := by rw [hadm]
        have hnot : e ∉ (τ * e⁻¹).cycleFactorsFinset := by
          rw [hfac]; simp
        simp only [toggle, hpick, if_neg hnot]
        simp
    · -- insertion
      have hT : toggle H τ = τ * e := by
        simp only [toggle, ← he_def, if_neg hmem]
      have hcdisj : ∀ c ∈ τ.cycleFactorsFinset, c.Disjoint e := by
        intro c hc
        by_cases hcw : 0 ≤ permWeight H c
        · exact hedisj c hc hcw
        · have hccyc : c.IsCycle := (Perm.mem_cycleFactorsFinset_iff.mp hc).1
          have hce : c ≠ e := by rintro rfl; exact hmem hc
          exact hB c e hccyc hecyc (lt_of_not_ge hcw) hew hce
      have hdisj : τ.Disjoint e := disjoint_of_forall_cycleFactors τ e hcdisj
      have hfac : (τ * e).cycleFactorsFinset = τ.cycleFactorsFinset ∪ {e} := by
        rw [hdisj.cycleFactorsFinset_mul_eq_union, hecyc.cycleFactorsFinset_eq_singleton]
      have hadm : admissible H (τ * e) = admissible H τ := by
        apply admissible_eq_of_cycleFactors
        intro c hc
        rw [hfac, Finset.mem_union, Finset.mem_singleton]
        constructor
        · rintro (h | rfl)
          · exact h
          · linarith
        · exact fun h => Or.inl h
      have hw : permWeight H (τ * e) = permWeight H τ * permWeight H e :=
        permWeight_mul_of_disjoint H hdiag hdisj
      refine ⟨by rw [hT, hadm], ?_, ?_, ?_⟩
      · rw [hT, hw, hew1]; ring
      · rw [hT]
        intro h
        apply hene
        have := congrArg (fun p => τ⁻¹ * p) h
        simpa [mul_assoc] using this
      · rw [hT]
        have hpick : pickPerm (admissible H (τ * e)) = e := by rw [hadm]
        have hin : e ∈ (τ * e).cycleFactorsFinset := by
          rw [hfac]; simp
        simp only [toggle, hpick, if_pos hin]
        simp
  have hcancel : ∑ τ ∈ Finset.univ.filter (fun τ => (admissible H τ).Nonempty),
      permWeight H τ = 0 := by
    refine Finset.sum_involution (fun τ _ => toggle H τ) ?_ ?_ ?_ ?_
    · intro τ hτ
      exact (key τ (Finset.mem_filter.mp hτ).2).2.1
    · intro τ hτ _
      exact (key τ (Finset.mem_filter.mp hτ).2).2.2.1
    · intro τ hτ
      have h := (key τ (Finset.mem_filter.mp hτ).2).1
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [h]
      exact (Finset.mem_filter.mp hτ).2
    · intro τ hτ
      exact (key τ (Finset.mem_filter.mp hτ).2).2.2.2
  rw [hcancel, zero_add]
  apply Finset.sum_nonneg
  intro τ hτ
  have hempty : ¬ (admissible H τ).Nonempty := (Finset.mem_filter.mp hτ).2
  apply permWeight_nonneg_of_cycleFactors H hdiag
  intro c hc
  by_contra hneg
  push_neg at hneg
  apply hempty
  refine ⟨c, ?_⟩
  have hccyc : c.IsCycle := (Perm.mem_cycleFactorsFinset_iff.mp hc).1
  simp only [admissible, negCycles, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨⟨hccyc, hneg⟩, ?_⟩
  intro c' hc' hw'
  have hne : c' ≠ c := by rintro rfl; linarith
  exact Perm.cycleFactorsFinset_pairwise_disjoint τ hc' hc hne

end DetCycle
end CRNT
