import CRNT.Theorems.DeficiencyZero.TreeConstantConstruction
import CRNT.Equilibria.TreePotentialIntegration
import CRNT.Deficiency.SteadyStateKernel

/-!
# Complete tree-potential assembly of the Deficiency Zero existence theorem

This file replaces the single opaque "integrate along a path" step in the constructive
Tree-Constant proof by the explicit residual/path theorem from `TreePotentialIntegration`.
The only deep remaining ingredients are therefore the directed Matrix--Tree theorem and the
finite-dimensional exact-sequence/Birch results already isolated elsewhere.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The exponential of the lifted tree potential satisfies the tree binomials, now by the
explicit path-integration theorem. -/
theorem exp_treePotential_satisfies_treeBinomials_complete
    (N : Network S) (κ : N.RateConstants) (hwr : N.WeaklyReversible)
    (hδ : N.DeficiencyZero) :
    ∃ x : Concentration S, x.Positive ∧ N.SatisfiesTreeConstantBinomials κ x := by
  obtain ⟨p, hp⟩ := N.exists_treePotential_of_deficiencyZero κ hwr hδ
  refine ⟨fun s => Real.exp (p s), fun s => Real.exp_pos _, ?_⟩
  exact N.exp_treePotential_satisfies_treeBinomials_from_edges κ hwr p hp

/-- Constructive positive complex-balanced existence from Matrix--Tree + deficiency zero. -/
theorem deficiencyZero_exists_complexBalanced_complete
    (N : Network S) (κ : N.RateConstants) (hwr : N.WeaklyReversible)
    (hδ : N.DeficiencyZero) :
    ∃ x : Concentration S, x.Positive ∧ N.IsComplexBalanced κ x := by
  obtain ⟨x, hx, hbin⟩ :=
    N.exp_treePotential_satisfies_treeBinomials_complete κ hwr hδ
  exact ⟨x, hx, N.complexBalanced_of_treeConstantBinomials κ hwr hx hbin⟩

/-- **Deficiency Zero Theorem, classwise existence form.** Every positive stoichiometric class
contains a positive complex-balanced equilibrium for every positive rate vector. -/
theorem deficiencyZero_existsUnique_complexBalanced_in_positiveClass_complete
    (N : Network S) (κ : N.RateConstants) (hwr : N.WeaklyReversible)
    (hδ : N.DeficiencyZero) {x₀ : Concentration S} (hx₀ : x₀.Positive) :
    ∃! x : Concentration S,
      x ∈ N.positiveCompatibilityClass x₀ ∧ N.IsComplexBalanced κ x := by
  obtain ⟨xstar, hxs, hcb⟩ := N.deficiencyZero_exists_complexBalanced_complete κ hwr hδ
  obtain ⟨x, hxmem, hxcb⟩ := N.exists_isComplexBalanced_in_positiveClass κ hxs hcb hx₀
  refine ⟨x, ⟨hxmem, hxcb⟩, ?_⟩
  rintro y ⟨hymem, hycb⟩
  exact N.isComplexBalanced_unique_in_positiveClass hwr κ hymem hxmem hycb hxcb

/-- Every positive mass-action steady state of a weakly reversible deficiency-zero network is
complex balanced. -/
theorem deficiencyZero_positiveSteadyState_isComplexBalanced_complete
    (N : Network S) (κ : N.RateConstants) (hwr : N.WeaklyReversible)
    (hδ : N.DeficiencyZero) {x : Concentration S} (hx : x.Positive)
    (hss : N.IsMassActionSteadyState κ x) : N.IsComplexBalanced κ x := by
  exact N.isComplexBalanced_of_steadyState_of_deficiencyZero hδ κ hss

end Network
end CRNT
