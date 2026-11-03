import CRNT.Equilibria.TreeConstantCriterion
import CRNT.Deficiency.ExactSequence
import CRNT.Theorems.DeficiencyZero.BirchExistence
import CRNT.Theorems.DeficiencyZero.Existence
import CRNT.Decision.Reachability

/-!
# Tree-constant construction of deficiency-zero equilibria

This is the classical Feinberg/Horn--Jackson proof written in tree-constant language.
Weak reversibility gives positive tree constants. Deficiency zero makes every compatible
set of logarithmic edge differences lift through the complex map to a species potential.
Exponentiating that potential realizes the tree-constant kernel vector as a mass-action
monomial vector and hence produces complex balance.
-/

namespace CRNT
namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Log tree-constant difference along a reaction edge. -/
noncomputable def treeLogDifference (N : Network S) (κ : N.RateConstants)
    (r : N.R) : ℝ :=
  Real.log (N.treeConstant κ (N.targetIdx r)) -
    Real.log (N.treeConstant κ (N.sourceIdx r))

/-- Under weak reversibility, tree-log differences are well-defined finite real numbers. -/
theorem treeConstant_positive_all (N : Network S) (κ : N.RateConstants)
    (hwr : N.WeaklyReversible) :
    ∀ c : N.ComplexIdx, 0 < N.treeConstant κ c :=
  N.treeConstant_pos_of_weaklyReversible κ hwr

/-- The tree-log edge vector lies in the incidence row space. -/
theorem treeLogDifference_mem_incidenceRowSpace (N : Network S)
    (κ : N.RateConstants) (hwr : N.WeaklyReversible) :
    N.treeLogDifference κ ∈ LinearMap.range (Matrix.transpose N.incidenceMatrix).mulVecLin := by
  refine ⟨fun c => Real.log (N.treeConstant κ c), ?_⟩
  funext r
  rw [N.incidenceTranspose_apply]
  rfl

/-- At deficiency zero, the tree-log edge differences lift to a species potential. -/
theorem exists_treePotential_of_deficiencyZero (N : Network S)
    (κ : N.RateConstants) (hwr : N.WeaklyReversible)
    (hδ : N.DeficiencyZero) :
    ∃ p : S → ℝ, ∀ r : N.R,
      ∑ s : S, N.reactionVector r s * p s = N.treeLogDifference κ r := by
  have hrow := N.treeLogDifference_mem_incidenceRowSpace κ hwr
  rw [← N.range_stoichTranspose_eq hδ] at hrow
  rcases hrow with ⟨p, hp⟩
  refine ⟨p, ?_⟩
  intro r
  have hr := congrFun hp r
  rw [N.stoichTranspose_apply, N.complexTranspose_apply, N.complexTranspose_apply] at hr
  rw [← hr]
  simp [Network.reactionVector_apply, sourceIdx, targetIdx, sub_mul,
    Finset.sum_sub_distrib]

/-- Exponentiating the tree potential realizes the tree-constant binomial equations. -/
theorem exp_treePotential_satisfies_treeBinomials (N : Network S)
    (κ : N.RateConstants) (hwr : N.WeaklyReversible)
    (hδ : N.DeficiencyZero) :
    ∃ x : Concentration S, x.Positive ∧ N.SatisfiesTreeConstantBinomials κ x := by
  obtain ⟨p, hp⟩ := N.exists_treePotential_of_deficiencyZero κ hwr hδ
  let x : Concentration S := fun s => Real.exp (p s)
  refine ⟨x, fun s => Real.exp_pos _, ?_⟩
  have hmon : ∀ c : N.ComplexIdx,
      N.complexMonomial x c = Real.exp (∑ s : S, (c.val s : ℝ) * p s) := by
    intro c
    change N.complexMonomialVector x c = _
    have hpos : 0 < N.complexMonomialVector x c :=
      Complex.massActionMonomial_pos (fun s => Real.exp_pos _) c.val
    have hlog : Real.log (N.complexMonomialVector x c) =
        ∑ s : S, (c.val s : ℝ) * p s := by
      rw [N.log_complexMonomialVector (fun s => Real.exp_pos _)]
      exact Finset.sum_congr rfl fun s _ => by
        simp [x]
    rw [← Real.exp_log hpos, hlog]
  have hedge : ∀ r : N.R,
      (∑ s : S, ((N.sourceIdx r).val s : ℝ) * p s) -
          Real.log (N.treeConstant κ (N.sourceIdx r)) =
      (∑ s : S, ((N.targetIdx r).val s : ℝ) * p s) -
          Real.log (N.treeConstant κ (N.targetIdx r)) := by
    intro r
    have hr := hp r
    simp only [Network.reactionVector_apply, treeLogDifference,
      sourceIdx, targetIdx, sub_mul] at hr ⊢
    rw [Finset.sum_sub_distrib] at hr
    linarith
  intro i j hij
  have hreach : N.Reaches i.1 j.1 := hwr.reaches_of_linked hij
  obtain ⟨k, hk⟩ := (N.reaches_iff_exists_reachesWithin i.1 j.1).1 hreach
  clear hij hreach
  have hres :
      (∑ s : S, (i.val s : ℝ) * p s) - Real.log (N.treeConstant κ i) =
      (∑ s : S, (j.val s : ℝ) * p s) - Real.log (N.treeConstant κ j) := by
    revert i
    induction k with
    | zero =>
        intro i hk
        have hij' : i = j := Subtype.ext hk
        simpa [hij']
    | succ k ih =>
        intro i hk
        rcases hk with hij' | ⟨r, hsrc, hrest⟩
        · have hij'' : i = j := Subtype.ext hij'
          simpa [hij'']
        · have hsi : N.sourceIdx r = i := by
            apply Subtype.ext
            simpa [sourceIdx] using hsrc
          calc
            (∑ s : S, (i.val s : ℝ) * p s) - Real.log (N.treeConstant κ i) =
                (∑ s : S, ((N.sourceIdx r).val s : ℝ) * p s) -
                  Real.log (N.treeConstant κ (N.sourceIdx r)) := by rw [hsi]
            _ = (∑ s : S, ((N.targetIdx r).val s : ℝ) * p s) -
                  Real.log (N.treeConstant κ (N.targetIdx r)) := hedge r
            _ = (∑ s : S, (j.val s : ℝ) * p s) -
                  Real.log (N.treeConstant κ j) := ih (N.targetIdx r) hrest
  have hratio := congrArg Real.exp hres
  rw [Real.exp_sub, Real.exp_sub,
    Real.exp_log (N.treeConstant_pos_of_weaklyReversible κ hwr i),
    Real.exp_log (N.treeConstant_pos_of_weaklyReversible κ hwr j),
    ← hmon i, ← hmon j] at hratio
  have hKi := (N.treeConstant_pos_of_weaklyReversible κ hwr i).ne'
  have hKj := (N.treeConstant_pos_of_weaklyReversible κ hwr j).ne'
  field_simp [hKi, hKj] at hratio
  simpa [mul_comm] using hratio

/-- Constructive tree-constant proof of existence of a positive complex-balanced state. -/
theorem exists_complexBalanced_via_treeConstants (N : Network S)
    (κ : N.RateConstants) (hwr : N.WeaklyReversible)
    (hδ : N.DeficiencyZero) :
    ∃ x : Concentration S, x.Positive ∧ N.IsComplexBalanced κ x := by
  obtain ⟨x, hx, hbin⟩ := N.exp_treePotential_satisfies_treeBinomials κ hwr hδ
  exact ⟨x, hx, N.complexBalanced_of_treeConstantBinomials κ hwr hx hbin⟩

/-- Tree constants plus Birch transport give the full classwise existence statement. -/
theorem exists_complexBalanced_in_class_via_treeConstants (N : Network S)
    (κ : N.RateConstants) (hwr : N.WeaklyReversible)
    (hδ : N.DeficiencyZero) {x₀ : Concentration S} (hx₀ : x₀.Positive) :
    ∃ x ∈ N.positiveCompatibilityClass x₀, N.IsComplexBalanced κ x := by
  obtain ⟨xstar, hxs, hcb⟩ := N.exists_complexBalanced_via_treeConstants κ hwr hδ
  exact N.exists_isComplexBalanced_in_positiveClass κ hxs hcb hx₀

end Network
end CRNT
