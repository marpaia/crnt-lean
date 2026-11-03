import CRNT.Theorems.DeficiencyOne.WeaklyReversibleExistence
import CRNT.Decision.Tactic

namespace CRNT.Examples.CatalyticChain
open CRNT Matrix
open scoped BigOperators

def source : Fin 4 → Complex (Fin 3)
  | 0 => ![1,0,1]
  | 1 => ![0,0,2]
  | 2 => ![0,0,2]
  | 3 => ![0,1,1]

def target : Fin 4 → Complex (Fin 3)
  | 0 => ![0,0,2]
  | 1 => ![1,0,1]
  | 2 => ![0,1,1]
  | 3 => ![0,0,2]

def rxn (r : Fin 4) : Reaction (Fin 3) := {source := source r, target := target r}

def N : Network (Fin 3) where
  R := Fin 4
  decEqR := inferInstance
  fintypeR := inferInstance
  reaction := rxn

theorem weaklyReversible : N.WeaklyReversible := by crnt_check
theorem numComplexes_eq : N.numComplexes = 3 := by decide
theorem complexes_eq : N.complexes = {source 0, source 1, target 2} := by decide

theorem linked_cAC : ∀ c ∈ N.complexes, N.Linked c (source 0) := by
  intro c hc
  rw [complexes_eq] at hc
  simp only [Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with rfl | rfl | rfl
  · exact Network.Linked.refl N (source 0)
  · exact (N.linked_of_reaction (0 : Fin 4)).symm
  · exact (N.linked_of_reaction (2 : Fin 4)).symm.trans
      (N.linked_of_reaction (0 : Fin 4)).symm

theorem numLinkageClasses_eq : N.numLinkageClasses = 1 := by
  have hss : Subsingleton (Quotient N.linkedSetoid) := by
    refine ⟨fun q q' => ?_⟩
    induction q using Quotient.inductionOn with
    | _ a =>
      induction q' using Quotient.inductionOn with
      | _ b =>
        exact Quotient.sound ((linked_cAC a.val a.2).trans (linked_cAC b.val b.2).symm)
  have hne : Nonempty (Quotient N.linkedSetoid) :=
    ⟨Quotient.mk _ ⟨source 0, N.source_mem_complexes (0 : Fin 4)⟩⟩
  exact Nat.card_eq_one_iff_unique.mpr ⟨hss, hne⟩

theorem rv0 : N.reactionVector (0 : Fin 4) = ![-1,0,1] := by
  funext s
  change ((target 0 s : ℝ) - (source 0 s : ℝ)) = _
  fin_cases s <;> norm_num [source, target]
theorem rv2 : N.reactionVector (2 : Fin 4) = ![0,1,-1] := by
  funext s
  change ((target 2 s : ℝ) - (source 2 s : ℝ)) = _
  fin_cases s <;> norm_num [source, target]
theorem rv1 : N.reactionVector (1 : Fin 4) = - N.reactionVector (0 : Fin 4) := by
  funext s
  change ((target 1 s : ℝ) - (source 1 s : ℝ)) = - ((target 0 s : ℝ) - (source 0 s : ℝ))
  fin_cases s <;> norm_num [source, target]
theorem rv3 : N.reactionVector (3 : Fin 4) = - N.reactionVector (2 : Fin 4) := by
  funext s
  change ((target 3 s : ℝ) - (source 3 s : ℝ)) = - ((target 2 s : ℝ) - (source 2 s : ℝ))
  fin_cases s <;> norm_num [source, target]
theorem rv0_ne : N.reactionVector (0 : Fin 4) ≠ 0 := by
  intro h; have hh := congrFun h 0; rw [rv0] at hh; norm_num at hh
theorem rv2_not_smul_rv0 : ∀ a : ℝ, a • N.reactionVector (0 : Fin 4) ≠ N.reactionVector (2 : Fin 4) := by
  intro a h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  rw [rv0, rv2] at h0 h1
  norm_num at h0 h1

def basis2 : Fin 2 → Concentration (Fin 3)
  | 0 => N.reactionVector (2 : Fin 4)
  | 1 => N.reactionVector (0 : Fin 4)

theorem basis2_li : LinearIndependent ℝ basis2 := by
  rw [linearIndependent_fin2]
  exact ⟨rv0_ne, rv2_not_smul_rv0⟩

theorem span_basis2_eq : Submodule.span ℝ (Set.range basis2) = N.stoichSubspace := by
  apply le_antisymm
  · apply Submodule.span_le.2
    rintro x ⟨i, rfl⟩
    fin_cases i <;> exact N.reactionVector_mem_stoichSubspace _
  · apply Submodule.span_le.2
    rintro x ⟨r, rfl⟩
    fin_cases r
    · apply Submodule.subset_span; exact ⟨1, rfl⟩
    · have h := rv1
      exact h ▸ Submodule.neg_mem _ (Submodule.subset_span ⟨1, rfl⟩)
    · apply Submodule.subset_span; exact ⟨0, rfl⟩
    · have h := rv3
      exact h ▸ Submodule.neg_mem _ (Submodule.subset_span ⟨0, rfl⟩)

theorem stoichRank_eq : N.stoichRank = 2 := by
  rw [Network.stoichRank, ← span_basis2_eq, finrank_span_eq_card basis2_li]
  decide

theorem deficiencyZero : N.DeficiencyZero := by
  rw [Network.deficiencyZero_iff_eq, numComplexes_eq, numLinkageClasses_eq, stoichRank_eq]

theorem conditions : N.DeficiencyOneConditions := by
  have hdef : N.deficiencyInt = 0 := deficiencyZero
  have hsumle := N.sum_linkageDeficiency_le_deficiency
  rw [hdef] at hsumle
  have hsumge : 0 ≤ ∑ q, N.linkageDeficiency q :=
    Finset.sum_nonneg fun q _ => N.linkageDeficiency_nonneg q
  have hsum : ∑ q, N.linkageDeficiency q = 0 := le_antisymm hsumle hsumge
  refine ⟨?_, ?_⟩
  · intro q
    have hq : N.linkageDeficiency q ≤ ∑ q', N.linkageDeficiency q' :=
      Finset.single_le_sum (fun q' _ => N.linkageDeficiency_nonneg q') (Finset.mem_univ q)
    rw [hsum] at hq
    omega
  · simpa [hdef] using hsum

theorem hypotheses : N.DeficiencyOneHypotheses :=
  ⟨conditions, weaklyReversible.oneTerminalSLCPerLinkageClass⟩

end CRNT.Examples.CatalyticChain
