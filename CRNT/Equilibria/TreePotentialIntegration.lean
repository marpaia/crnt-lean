import CRNT.Theorems.DeficiencyZero.TreeConstantConstruction
import CRNT.Graph.WeakReversibility
import CRNT.Decision.Reachability

/-!
# Integrating the tree-log potential on linkage classes

The deficiency-zero tree-constant construction produces a species vector `p` whose reaction
increments reproduce the logarithmic tree-constant increments.  This file isolates the
remaining path-integration argument.

For a complex `y`, define

`ρ(y) = <y,p> - log K_y`.

The reaction-edge identity says `ρ` is unchanged by every reaction.  Hence `ρ` is constant
on every directed path and, under weak reversibility, on each linkage class.  Exponentiating
this classwise equality gives the tree-constant binomials directly.
-/

namespace CRNT
namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Pairing of a complex with a species logarithmic potential. -/
def complexTreePotential (c : Complex S) (p : S → ℝ) : ℝ :=
  ∑ s : S, (c s : ℝ) * p s

/-- Residual between a species potential and the logarithmic tree constant. -/
noncomputable def treePotentialResidual (N : Network S) (κ : N.RateConstants)
    (p : S → ℝ) (c : N.ComplexIdx) : ℝ :=
  complexTreePotential c.1 p - Real.log (N.treeConstant κ c)

/-- A reaction increment of the complex potential is the reaction vector paired with `p`. -/
theorem complexTreePotential_target_sub_source (N : Network S) (r : N.R) (p : S → ℝ) :
    complexTreePotential (N.reaction r).target p - complexTreePotential (N.reaction r).source p =
      ∑ s : S, N.reactionVector r s * p s := by
  simp [complexTreePotential, Network.reactionVector_apply, sub_mul,
    Finset.sum_sub_distrib]

/-- If `p` lifts the tree-log edge differences, the residual is constant across one reaction. -/
theorem treePotentialResidual_eq_of_reaction
    (N : Network S) (κ : N.RateConstants) (p : S → ℝ)
    (hp : ∀ r : N.R,
      ∑ s : S, N.reactionVector r s * p s = N.treeLogDifference κ r)
    (r : N.R) :
    N.treePotentialResidual κ p (N.sourceIdx r) =
      N.treePotentialResidual κ p (N.targetIdx r) := by
  have hpot := N.complexTreePotential_target_sub_source r p
  have hedge := hp r
  -- Substitute both increments.  The tree-log increment was defined as
  -- `log K_target - log K_source`.
  unfold treePotentialResidual
  unfold treeLogDifference at hedge
  dsimp [sourceIdx, targetIdx] at hpot hedge ⊢
  linarith

/-- Residual equality propagates along a directed reaction path. -/
theorem treePotentialResidual_eq_of_reaches
    (N : Network S) (κ : N.RateConstants) (p : S → ℝ)
    (hp : ∀ r : N.R,
      ∑ s : S, N.reactionVector r s * p s = N.treeLogDifference κ r)
    {c d : N.ComplexIdx}
    (hreach : N.Reaches c.1 d.1) :
    N.treePotentialResidual κ p c = N.treePotentialResidual κ p d := by
  obtain ⟨k, hk⟩ := (N.reaches_iff_exists_reachesWithin c.1 d.1).1 hreach
  clear hreach
  revert c
  induction k with
  | zero =>
      intro c hk
      have hcd : c.1 = d.1 := hk
      have hcd' : c = d := Subtype.ext hcd
      simpa [hcd']
  | succ k ih =>
      intro c hk
      rcases hk with hcd | ⟨r, hsrc, hrest⟩
      · have hcd' : c = d := Subtype.ext hcd
        simpa [hcd']
      · have hsc : N.sourceIdx r = c := by
          apply Subtype.ext
          simpa [sourceIdx] using hsrc
        calc
          N.treePotentialResidual κ p c =
              N.treePotentialResidual κ p (N.sourceIdx r) := by rw [hsc]
          _ = N.treePotentialResidual κ p (N.targetIdx r) :=
            N.treePotentialResidual_eq_of_reaction κ p hp r
          _ = N.treePotentialResidual κ p d := ih hrest

/-- Under weak reversibility, the residual is constant on each linkage class. -/
theorem treePotentialResidual_eq_of_linked
    (N : Network S) (κ : N.RateConstants) (hwr : N.WeaklyReversible)
    (p : S → ℝ)
    (hp : ∀ r : N.R,
      ∑ s : S, N.reactionVector r s * p s = N.treeLogDifference κ r)
    {c d : N.ComplexIdx} (hcd : N.Linked c.1 d.1) :
    N.treePotentialResidual κ p c = N.treePotentialResidual κ p d := by
  have hreach : N.Reaches c.1 d.1 := hwr.reaches_of_linked hcd
  exact N.treePotentialResidual_eq_of_reaches κ p hp hreach

/-- Exponentiating a lifted tree potential gives the classwise tree-constant ratio. -/
theorem exp_complexTreePotential_treeConstant_ratio
    (N : Network S) (κ : N.RateConstants) (hwr : N.WeaklyReversible)
    (p : S → ℝ)
    (hp : ∀ r : N.R,
      ∑ s : S, N.reactionVector r s * p s = N.treeLogDifference κ r)
    {c d : N.ComplexIdx} (hcd : N.Linked c.1 d.1) :
    Real.exp (complexTreePotential c.1 p) / N.treeConstant κ c =
      Real.exp (complexTreePotential d.1 p) / N.treeConstant κ d := by
  have hres := N.treePotentialResidual_eq_of_linked κ hwr p hp hcd
  have hKc := (N.treeConstant_pos_of_weaklyReversible κ hwr c).ne'
  have hKd := (N.treeConstant_pos_of_weaklyReversible κ hwr d).ne'
  have hexp := congrArg Real.exp hres
  unfold treePotentialResidual at hexp
  rw [Real.exp_sub, Real.exp_sub,
    Real.exp_log (N.treeConstant_pos_of_weaklyReversible κ hwr c),
    Real.exp_log (N.treeConstant_pos_of_weaklyReversible κ hwr d)] at hexp
  exact hexp

/-- Monomials of `x_s = exp(p_s)` are exponentials of the complex potential. -/
theorem complexMonomial_exp_potential (N : Network S) (p : S → ℝ)
    (c : N.ComplexIdx) :
    N.complexMonomial (fun s => Real.exp (p s)) c =
      Real.exp (complexTreePotential c.1 p) := by
  simp only [complexMonomial, Complex.massActionMonomial, complexTreePotential]
  calc
    (∏ s : S, Real.exp (p s) ^ c.val s) =
        ∏ s : S, Real.exp ((c.val s : ℝ) * p s) := by
      refine Finset.prod_congr rfl fun s _ => ?_
      rw [← Real.exp_nat_mul]
    _ = Real.exp (∑ s : S, (c.val s : ℝ) * p s) := by
      rw [Real.exp_sum]

/-- The path-integration lemma closes the tree-binomial step of the deficiency-zero proof. -/
theorem exp_treePotential_satisfies_treeBinomials_from_edges
    (N : Network S) (κ : N.RateConstants) (hwr : N.WeaklyReversible)
    (p : S → ℝ)
    (hp : ∀ r : N.R,
      ∑ s : S, N.reactionVector r s * p s = N.treeLogDifference κ r) :
    N.SatisfiesTreeConstantBinomials κ (fun s => Real.exp (p s)) := by
  intro i j hij
  have hratio := N.exp_complexTreePotential_treeConstant_ratio κ hwr p hp hij
  rw [N.complexMonomial_exp_potential p i, N.complexMonomial_exp_potential p j]
  have hKi := (N.treeConstant_pos_of_weaklyReversible κ hwr i).ne'
  have hKj := (N.treeConstant_pos_of_weaklyReversible κ hwr j).ne'
  field_simp at hratio ⊢
  nlinarith

end Network
end CRNT
