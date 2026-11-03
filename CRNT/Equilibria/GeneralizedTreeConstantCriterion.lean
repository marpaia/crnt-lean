import CRNT.Equilibria.TreeConstantCriterion
import CRNT.Kinetics.GeneralizedNetwork

/-!
# Tree-constant criterion for generalized mass-action systems

The kinetic graph and its tree constants depend only on the reaction graph and rate constants, not
on the kinetic-order complexes.  In a generalized mass-action system the ordinary complex monomial
`x^y` is therefore replaced by the kinetic monomial `x^{\tilde y}` attached to the source complex.
On a weakly reversible graph, generalized complex balance is equivalent to the same linkage-class
tree-constant binomials with those kinetic monomials.
-/

namespace CRNT
namespace Network
namespace GeneralizedMassActionData

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]
variable {N : Network S}

/-- Kinetic monomial vector indexed by stoichiometric graph complexes. -/
noncomputable def kineticMonomialVector (G : N.GeneralizedMassActionData) (x : Concentration S) :
    N.ComplexIdx → ℝ :=
  fun c => G.kineticMonomial (G.kineticComplex c) x

/-- Generalized complex balance is kinetic-Laplacian annihilation of the kinetic monomial vector. -/
theorem isComplexBalanced_iff_kineticMonomial_kineticKernel
    (G : N.GeneralizedMassActionData) (κ : N.RateConstants) (x : Concentration S) :
    G.IsComplexBalanced κ x ↔ N.kineticMap κ (G.kineticMonomialVector x) = 0 := by
  have happly : ∀ c : N.ComplexIdx,
      N.kineticMap κ (G.kineticMonomialVector x) c =
        G.inflow κ x c - G.outflow κ x c := by
    intro c
    rw [N.kineticMap_apply, GeneralizedMassActionData.inflow,
      GeneralizedMassActionData.outflow, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro r _
    unfold GeneralizedMassActionData.generalizedRate kineticMonomialVector
    by_cases ht : N.targetIdx r = c <;>
      by_cases hs : N.sourceIdx r = c <;> simp [ht, hs] <;> ring
  constructor
  · intro hcb
    funext c
    rw [happly c, Pi.zero_apply, sub_eq_zero]
    exact hcb c
  · intro hker c
    have hc := congrFun hker c
    rw [happly c, Pi.zero_apply, sub_eq_zero] at hc
    exact hc

/-- Generalized tree-constant binomial relations. -/
def SatisfiesTreeConstantBinomials
    (G : N.GeneralizedMassActionData) (κ : N.RateConstants)
    (x : Concentration S) : Prop :=
  ∀ i j : N.ComplexIdx, N.Linked i.1 j.1 →
    N.treeConstant κ j * G.kineticMonomial (G.kineticComplex i) x =
      N.treeConstant κ i * G.kineticMonomial (G.kineticComplex j) x

/-- Generalized complex balance implies the tree-constant binomials. -/
theorem satisfiesTreeConstantBinomials_of_complexBalanced
    (G : N.GeneralizedMassActionData) (κ : N.RateConstants)
    (hwr : N.WeaklyReversible) {x : Concentration S}
    (hcb : G.IsComplexBalanced κ x) :
    G.SatisfiesTreeConstantBinomials κ x := by
  classical
  have hker : N.kineticMap κ (G.kineticMonomialVector x) = 0 :=
    (G.isComplexBalanced_iff_kineticMonomial_kineticKernel κ x).1 hcb
  obtain ⟨a, ha⟩ := N.exists_treeConstant_class_coefficients κ hwr hker
  have hparam : ∀ c : N.ComplexIdx,
      G.kineticMonomial (G.kineticComplex c) x =
        a (N.classOf c) * N.treeConstant κ c := by
    intro c
    have hc := congrFun ha c
    simpa [kineticMonomialVector, classTreeVector] using hc
  intro i j hij
  rw [hparam i, hparam j]
  have hclass : N.classOf i = N.classOf j := Quotient.sound hij
  rw [hclass]
  ring

/-- On a weakly reversible graph, generalized tree-constant binomials imply generalized complex
balance. -/
theorem complexBalanced_of_treeConstantBinomials
    (G : N.GeneralizedMassActionData) (κ : N.RateConstants)
    (hwr : N.WeaklyReversible) {x : Concentration S}
    (hbin : G.SatisfiesTreeConstantBinomials κ x) :
    G.IsComplexBalanced κ x := by
  classical
  let rep : Quotient N.linkedSetoid → N.ComplexIdx :=
    fun q => Classical.choose (Quotient.exists_rep q)
  have hrep (q : Quotient N.linkedSetoid) : N.classOf (rep q) = q := by
    simpa [rep, classOf] using (Classical.choose_spec (Quotient.exists_rep q))
  let a : Quotient N.linkedSetoid → ℝ := fun q =>
    G.kineticMonomial (G.kineticComplex (rep q)) x / N.treeConstant κ (rep q)
  have hparam : ∀ c : N.ComplexIdx,
      G.kineticMonomial (G.kineticComplex c) x =
        a (N.classOf c) * N.treeConstant κ c := by
    intro c
    have hlinked : N.Linked c.val (rep (N.classOf c)).val := by
      exact Quotient.exact ((hrep (N.classOf c)).symm)
    have hbin' := hbin c (rep (N.classOf c)) hlinked
    have hK : 0 < N.treeConstant κ (rep (N.classOf c)) :=
      N.treeConstant_pos_of_weaklyReversible κ hwr _
    dsimp [a]
    field_simp [hK.ne']
    simpa [mul_comm] using hbin'
  apply (G.isComplexBalanced_iff_kineticMonomial_kineticKernel κ x).2
  have hv : G.kineticMonomialVector x = N.treeKernelCoordinates κ a := by
    funext c
    change G.kineticMonomial (G.kineticComplex c) x =
      N.treeKernelCoordinates κ a c
    rw [hparam c]
    simp [treeKernelCoordinates, classTreeVector]
  rw [hv, ← LinearMap.mem_ker,
    ← N.range_treeKernelCoordinates_eq_kineticKernel κ hwr]
  exact ⟨a, rfl⟩

/-- **Generalized tree-constant criterion.** -/
theorem complexBalanced_iff_treeConstantBinomials
    (G : N.GeneralizedMassActionData) (κ : N.RateConstants)
    (hwr : N.WeaklyReversible) {x : Concentration S} :
    G.IsComplexBalanced κ x ↔ G.SatisfiesTreeConstantBinomials κ x :=
  ⟨G.satisfiesTreeConstantBinomials_of_complexBalanced κ hwr,
    G.complexBalanced_of_treeConstantBinomials κ hwr⟩

/-- Linkage-class scalar parametrization of a generalized CBE kinetic-monomial vector. -/
theorem exists_linkage_scalars_of_complexBalanced
    (G : N.GeneralizedMassActionData) (κ : N.RateConstants)
    (hwr : N.WeaklyReversible) {x : Concentration S}
    (hcb : G.IsComplexBalanced κ x) :
    ∃ a : Quotient N.linkedSetoid → ℝ,
      (∀ q, 0 < a q) ∧
      ∀ c : N.ComplexIdx,
        G.kineticMonomial (G.kineticComplex c) x =
          a (N.classOf c) * N.treeConstant κ c := by
  classical
  have hker : N.kineticMap κ (G.kineticMonomialVector x) = 0 :=
    (G.isComplexBalanced_iff_kineticMonomial_kineticKernel κ x).1 hcb
  have hpos : ∀ c : N.ComplexIdx, 0 < G.kineticMonomialVector x c := by
    intro c
    exact G.kineticMonomial_pos (G.kineticComplex c) x
  obtain ⟨a, ha, hv⟩ :=
    (N.positive_kineticKernel_iff_treeCoefficients κ hwr (G.kineticMonomialVector x)).1
      ⟨hker, hpos⟩
  refine ⟨a, ha, ?_⟩
  intro c
  have hc := congrFun hv c
  simpa [kineticMonomialVector, treeKernelCoordinates, classTreeVector] using hc

/-- Conversely, a positive classwise tree-constant parametrization is generalized complex balance. -/
theorem complexBalanced_of_linkage_scalars
    (G : N.GeneralizedMassActionData) (κ : N.RateConstants)
    (hwr : N.WeaklyReversible) {x : Concentration S}
    {a : Quotient N.linkedSetoid → ℝ}
    (ha : ∀ q, 0 < a q)
    (hparam : ∀ c : N.ComplexIdx,
      G.kineticMonomial (G.kineticComplex c) x =
        a (N.classOf c) * N.treeConstant κ c) :
    G.IsComplexBalanced κ x := by
  apply G.complexBalanced_of_treeConstantBinomials κ hwr
  intro i j hij
  rw [hparam i, hparam j]
  have hclass : N.classOf i = N.classOf j := Quotient.sound hij
  rw [hclass]
  ring

end GeneralizedMassActionData
end Network
end CRNT
