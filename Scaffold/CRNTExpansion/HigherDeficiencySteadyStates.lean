import CRNT.Deficiency.HigherDeficiency
import CRNT.Deficiency.SteadyStateKernel
import CRNT.Multistationarity.Capacity

/-!
# Higher-deficiency localization of steady-state imbalance

`HigherDeficiency` proves that under a tight linkage-deficiency decomposition the global deficiency
subspace is the internal direct sum of the per-linkage-class deficiency subspaces.  This scaffold
connects that structural theorem to the mass-action steady-state equation.

At a steady state, `A_k Psi(x)` lies in the global deficiency subspace.  Tightness therefore
localizes its restriction to each linkage class.  In particular every deficiency-zero linkage
class has zero kinetic imbalance; only genuinely deficient linkage classes can carry the residual
complex imbalance of a species-level steady state.

This is the right entry point for higher-deficiency existence/multistationarity criteria: future
criteria should operate on the finite collection of nontrivial per-class deficiency modes rather
than on the full complex space.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- At a mass-action steady state of a tight network, each linkage-class restriction of the kinetic
imbalance lies in that class's deficiency subspace. -/
theorem restrictToClass_kineticImage_mem_linkageDeficiencySubspace_of_tight
    (N : Network S) (h : N.TightLinkageDeficiency) (κ : N.RateConstants)
    {x : Concentration S} (hx : N.IsMassActionSteadyState κ x)
    (q : Quotient N.linkedSetoid) :
    N.restrictToClass q (N.kineticMap κ (N.complexMonomialVector x)) ∈
      N.linkageDeficiencySubspace q := by
  exact N.restrictToClass_mem_linkageDeficiencySubspace_of_tight h
    (N.kineticMap_complexMonomial_mem_deficiencySubspace κ hx) q

/-- A deficiency-zero linkage class carries no complex imbalance at any mass-action steady state,
provided the linkage decomposition is tight. -/
theorem restrictToClass_kineticImage_eq_zero_of_linkageDeficiency_zero_of_tight
    (N : Network S) (h : N.TightLinkageDeficiency) (κ : N.RateConstants)
    {x : Concentration S} (hx : N.IsMassActionSteadyState κ x)
    (q : Quotient N.linkedSetoid) (hq : N.linkageDeficiency q = 0) :
    N.restrictToClass q (N.kineticMap κ (N.complexMonomialVector x)) = 0 := by
  have hmem :=
    N.restrictToClass_kineticImage_mem_linkageDeficiencySubspace_of_tight h κ hx q
  rw [N.linkageDeficiencySubspace_eq_bot_of_deficiency_zero hq, Submodule.mem_bot] at hmem
  exact hmem

/-- Equivalently, the steady-state kinetic imbalance is supported only on the deficient linkage
classes. -/
theorem steadyState_kineticImage_zero_off_deficientClasses_of_tight
    (N : Network S) (h : N.TightLinkageDeficiency) (κ : N.RateConstants)
    {x : Concentration S} (hx : N.IsMassActionSteadyState κ x) :
    ∀ q : Quotient N.linkedSetoid, q ∉ N.deficientLinkageClasses ->
      N.restrictToClass q (N.kineticMap κ (N.complexMonomialVector x)) = 0 := by
  intro q hq
  have hnot : ¬ 1 ≤ N.linkageDeficiency q := by
    intro hpos
    exact hq ((N.mem_deficientLinkageClasses q).2 hpos)
  have hnonneg := N.linkageDeficiency_nonneg q
  have hzero : N.linkageDeficiency q = 0 := by omega
  exact N.restrictToClass_kineticImage_eq_zero_of_linkageDeficiency_zero_of_tight
    h κ hx q hzero

/-- For a steady state of a tight network, complex balance is equivalent to vanishing of the
kinetic imbalance on the finitely many deficient linkage classes.  Nondeficient classes vanish
automatically by the preceding localization theorem.  This reduces higher-deficiency complex
balance to the genuinely nontrivial local deficiency modes. -/
theorem isComplexBalanced_iff_zero_on_deficientClasses_of_tight
    (N : Network S) (h : N.TightLinkageDeficiency) (κ : N.RateConstants)
    {x : Concentration S} (hss : N.IsMassActionSteadyState κ x) :
    N.IsComplexBalanced κ x ↔
      ∀ q : Quotient N.linkedSetoid, q ∈ N.deficientLinkageClasses ->
        N.restrictToClass q (N.kineticMap κ (N.complexMonomialVector x)) = 0 := by
  constructor
  · intro hcb q _hq
    have hzero : N.kineticMap κ (N.complexMonomialVector x) = 0 :=
      (N.isComplexBalanced_iff_kineticMap κ x).mp hcb
    rw [hzero]
    funext c
    simp [restrictToClass]
  · intro hdef
    apply (N.isComplexBalanced_iff_kineticMap κ x).mpr
    rw [← N.sum_restrictToClass (N.kineticMap κ (N.complexMonomialVector x))]
    apply Finset.sum_eq_zero
    intro q _
    by_cases hq : q ∈ N.deficientLinkageClasses
    · exact hdef q hq
    · exact N.steadyState_kineticImage_zero_off_deficientClasses_of_tight h κ hss q hq

/-- If a tight network has no deficient linkage classes, every mass-action steady state is already
complex-balanced.  This recovers the deficiency-zero mechanism from the higher-deficiency
localization API without appealing to a global dimension argument at the call site. -/
theorem isComplexBalanced_of_no_deficientClasses_of_tight
    (N : Network S) (h : N.TightLinkageDeficiency)
    (hno : N.deficientLinkageClasses = ∅) (κ : N.RateConstants)
    {x : Concentration S} (hss : N.IsMassActionSteadyState κ x) :
    N.IsComplexBalanced κ x := by
  apply (N.isComplexBalanced_iff_zero_on_deficientClasses_of_tight h κ hss).mpr
  intro q hq
  rw [hno] at hq
  simp at hq

end Network
end CRNT
