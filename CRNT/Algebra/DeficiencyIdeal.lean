import CRNT.Algebra.SteadyStateIdeal
import CRNT.Deficiency.ExactSequence
import CRNT.Deficiency.SteadyStateKernel

/-!
# Deficiency and algebraic complex-balance constraints

Deficiency measures the linear gap between incidence balance and species balance.  At
the polynomial level the same gap appears between the complex-balance equations and the
species steady-state equations.  This file records that relationship as a map of free
modules of polynomial equations.
-/

namespace CRNT
namespace Network

open MvPolynomial

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Polynomial-valued complex imbalance vector. -/
noncomputable def complexBalancePolynomialVector (N : Network S)
    (κ : N.RateConstants) : N.ComplexIdx → MvPolynomial S ℝ :=
  fun c => N.complexBalancePolynomial κ c

/-- Polynomial-valued species steady-state vector. -/
noncomputable def steadyStatePolynomialVector (N : Network S)
    (κ : N.RateConstants) : S → MvPolynomial S ℝ :=
  fun s => N.steadyStatePolynomial κ s

/-- Species steady-state equations are obtained from complex imbalance by applying the
complex map coefficientwise. -/
theorem steadyStatePolynomialVector_eq_complexMap
    (N : Network S) (κ : N.RateConstants) :
    ∀ s : S,
      N.steadyStatePolynomialVector κ s =
        ∑ c : N.ComplexIdx, C (c.val s : ℝ) *
          N.complexBalancePolynomialVector κ c := by
  exact N.steadyStatePolynomial_eq_complexBalanceCombination κ

/-- At a species steady state, the evaluated complex imbalance lies in the deficiency
space.  This is the polynomial/evaluation version of the standard steady-state-kernel
lemma. -/
theorem evaluated_complexImbalance_mem_deficiencySubspace
    (N : Network S) (κ : N.RateConstants) {x : Concentration S}
    (hss : N.massActionVectorField κ x = 0) :
    (fun c => eval x (N.complexBalancePolynomial κ c)) ∈ N.deficiencySubspace := by
  have hx : N.IsMassActionSteadyState κ x := by
    intro s
    exact congrFun hss s
  have hkin := N.kineticMap_complexMonomial_mem_deficiencySubspace κ hx
  have heq : (fun c => eval x (N.complexBalancePolynomial κ c)) =
      N.kineticMap κ (N.complexMonomialVector x) := by
    funext c
    rw [N.eval_complexBalancePolynomial κ c x,
      N.kineticMap_complexMonomial_apply κ x c]
  rwa [heq]

/-- Deficiency zero collapses species steady state and complex balance on the positive
orthant (indeed algebraically at every concentration for the evaluated imbalance). -/
theorem complexBalanced_of_steadyState_deficiencyZero_polynomial
    (N : Network S) (κ : N.RateConstants) (hδ : N.DeficiencyZero)
    {x : Concentration S} (hss : N.massActionVectorField κ x = 0) :
    N.IsComplexBalanced κ x := by
  have hD := N.evaluated_complexImbalance_mem_deficiencySubspace κ hss
  have hbot := N.deficiencyZero_iff_deficiencySubspace_eq_bot.mp hδ
  rw [hbot, Submodule.mem_bot] at hD
  intro c hc
  let ci : N.ComplexIdx := ⟨c, hc⟩
  have hci := congrFun hD ci
  rw [N.eval_complexBalancePolynomial κ ci x] at hci
  exact sub_eq_zero.mp hci

/-- In deficiency zero, the positive steady-state variety and positive complex-balance
variety coincide. -/
theorem positive_steadyState_iff_complexBalanced_of_deficiencyZero
    (N : Network S) (κ : N.RateConstants) (hδ : N.DeficiencyZero)
    {x : Concentration S} (hx : x.Positive) :
    N.massActionVectorField κ x = 0 ↔ N.IsComplexBalanced κ x := by
  constructor
  · exact N.complexBalanced_of_steadyState_deficiencyZero_polynomial κ hδ
  · intro hcb
    funext s
    exact hcb.isMassActionSteadyState N κ s

end Network
end CRNT
