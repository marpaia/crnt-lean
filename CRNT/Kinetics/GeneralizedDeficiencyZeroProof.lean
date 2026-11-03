import CRNT.Kinetics.GeneralizedDeficiencyZeroExistence
import CRNT.Kinetics.GeneralizedComplexBalanceObstruction
import CRNT.Equilibria.GeneralizedTreeConstantCriterion
import CRNT.Deficiency.TerminalKernelDimension

/-!
# Proof architecture for the generalized deficiency-zero theorem

The generalized theorem naturally factors into three independent pieces:

1. **graph algebra:** weak reversibility gives positive tree constants;
2. **kinetic deficiency:** `\tilde δ = 0` lifts tree-constant log differences to a
   species log-potential, producing one positive generalized CBE `x*`;
3. **Birch/oriented-matroid geometry:** closure + face conditions make the toric leaf
   through `x*` meet every positive stoichiometric class, and sign compatibility makes
   the intersection unique and transverse.

This file records those intermediate objects explicitly so the generalized theorem no
longer appears as a single black-box existence statement.
-/

namespace CRNT
namespace Network
namespace GeneralizedMassActionData

variable {S : Type} [DecidableEq S] [Fintype S]
variable {N : Network S}

/-- A log-potential realizes the tree-constant ratios through kinetic-order complexes. -/
def IsTreeLogPotential (G : N.GeneralizedMassActionData)
    (κ : N.RateConstants) (z : S → ℝ) : Prop :=
  ∀ i j : N.ComplexIdx, N.Linked i.1 j.1 →
    ∑ s : S, (G.kineticComplex j s - G.kineticComplex i s) * z s =
      Real.log (N.treeConstant κ j) - Real.log (N.treeConstant κ i)

/-- Kinetic deficiency zero produces a tree log-potential on every weakly reversible graph. -/
theorem exists_treeLogPotential_of_kineticDeficiencyZero
    (G : N.GeneralizedMassActionData) (κ : N.RateConstants)
    (hwr : N.WeaklyReversible) (hδk : G.kineticDeficiency = 0) :
    ∃ z : S → ℝ, G.IsTreeLogPotential κ z := by
  simpa [IsTreeLogPotential] using
    G.exists_logTreeSolution_of_kineticDeficiency_zero κ hwr hδk

/-- Exponential image of a tree log-potential. -/
noncomputable def concentrationOfLogPotential (z : S → ℝ) : Concentration S :=
  fun s => Real.exp (z s)

@[simp] theorem concentrationOfLogPotential_pos (z : S → ℝ) :
    (concentrationOfLogPotential z).Positive := by
  intro s
  exact Real.exp_pos _

/-- A tree log-potential satisfies the generalized tree-constant binomials after
exponentiation. -/
theorem treeLogPotential_satisfiesTreeConstantBinomials
    (G : N.GeneralizedMassActionData) (κ : N.RateConstants)
    (hwr : N.WeaklyReversible) {z : S → ℝ}
    (hz : G.IsTreeLogPotential κ z) :
    G.SatisfiesTreeConstantBinomials κ (concentrationOfLogPotential z) := by
  apply (G.treeConstantBinomials_iff_logTreeEquations κ hwr
    (concentrationOfLogPotential_pos z)).2
  intro i j hij
  simpa [SatisfiesLogTreeEquations, concentrationOfLogPotential] using hz i j hij

/-- Hence kinetic deficiency zero constructs one positive generalized CBE. -/
theorem referenceComplexBalanced_of_kineticDeficiencyZero
    (G : N.GeneralizedMassActionData) (κ : N.RateConstants)
    (hwr : N.WeaklyReversible) (hδk : G.kineticDeficiency = 0) :
    ∃ xstar : Concentration S,
      xstar.Positive ∧ G.IsComplexBalanced κ xstar := by
  obtain ⟨z, hz⟩ := G.exists_treeLogPotential_of_kineticDeficiencyZero κ hwr hδk
  refine ⟨concentrationOfLogPotential z, concentrationOfLogPotential_pos z, ?_⟩
  exact G.complexBalanced_of_treeConstantBinomials κ hwr
    (G.treeLogPotential_satisfiesTreeConstantBinomials κ hwr hz)

/-- All generalized CBEs lie on the kinetic-order toric leaf through one reference CBE. -/
theorem complexBalanced_set_eq_reference_toricLeaf
    (G : N.GeneralizedMassActionData) (κ : N.RateConstants)
    (hwr : N.WeaklyReversible)
    {xstar : Concentration S} (hxs : xstar.Positive)
    (hcbs : G.IsComplexBalanced κ xstar) :
    {x : Concentration S | x.Positive ∧ G.IsComplexBalanced κ x} =
      {x : Concentration S | x.Positive ∧
        (fun s => Real.log (x s) - Real.log (xstar s)) ∈
          orthSum G.kineticOrderSubspace} := by
  ext x
  constructor
  · intro hx
    exact ⟨hx.1, G.logRatio_mem_orth_kineticOrderSubspace κ hwr
      hx.1 hxs hx.2 hcbs⟩
  · intro hx
    exact ⟨hx.1, G.complexBalanced_of_toricLeaf κ hwr hxs hcbs ⟨hx.1, hx.2⟩⟩

/-- Closure and face conditions turn one reference CBE into existence in every positive
stoichiometric class. -/
theorem exists_in_every_class_from_reference
    (G : N.GeneralizedMassActionData) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive)
    (hcbs : G.IsComplexBalanced κ xstar)
    (hclosure : GeneralizedClosureCondition N.stoichSubspace G.kineticOrderSubspace)
    (hface : GeneralizedFaceCondition N.stoichSubspace G.kineticOrderSubspace)
    {c : Concentration S} (hc : c.Positive) :
    ∃ x : Concentration S,
      x.Positive ∧ N.SameStoichClass x c ∧ G.IsComplexBalanced κ x := by
  obtain ⟨x, hx⟩ := generalized_birch_existence_of_conditions
    N.stoichSubspace G.kineticOrderSubspace hclosure xstar c hxs hc
  refine ⟨x, hx.1, ?_, ?_⟩
  · exact hx.2.1
  · have hwr : N.WeaklyReversible := by
      apply N.weaklyReversible_of_exists_positive_kineticKernel κ
      refine ⟨G.kineticMonomialVector xstar, ?_, ?_⟩
      · intro i
        exact G.kineticMonomial_pos _ _
      · exact (G.isComplexBalanced_iff_kineticMonomial_kineticKernel κ xstar).1 hcbs
    exact G.complexBalanced_of_toricLeaf κ hwr hxs hcbs ⟨hx.1, hx.2.2⟩

/-- Full generalized deficiency-zero theorem decomposed through a constructed reference
CBE and generalized Birch intersection. -/
theorem generalizedDeficiencyZero_existsUnique_constructive
    (G : N.GeneralizedMassActionData) (κ : N.RateConstants)
    (hwr : N.WeaklyReversible) (hδk : G.kineticDeficiency = 0)
    (hclosure : GeneralizedClosureCondition N.stoichSubspace G.kineticOrderSubspace)
    (hface : GeneralizedFaceCondition N.stoichSubspace G.kineticOrderSubspace)
    (hsign : SignCompatible N.stoichSubspace (orthSum G.kineticOrderSubspace))
    {c : Concentration S} (hc : c.Positive) :
    ∃! x : Concentration S,
      x.Positive ∧ N.SameStoichClass x c ∧ G.IsComplexBalanced κ x := by
  obtain ⟨xstar, hxs, hcbs⟩ :=
    G.referenceComplexBalanced_of_kineticDeficiencyZero κ hwr hδk
  obtain ⟨x, hx, hclass, hcb⟩ :=
    G.exists_in_every_class_from_reference κ hxs hcbs hclosure hface hc
  refine ⟨x, ⟨hx, hclass, hcb⟩, ?_⟩
  intro y hy
  exact G.complexBalanced_unique_in_stoichClass_of_signCompatible κ hwr hsign
    hy.1 hx hy.2.2 hcb (by
      change y - x ∈ N.stoichSubspace
      have hdiff : y - x = (y - c) - (x - c) := by ring
      rw [hdiff]
      exact N.stoichSubspace.sub_mem hy.2.1 hclass)

end GeneralizedMassActionData
end Network
end CRNT
