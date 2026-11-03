import CRNT.Theorems.DeficiencyZero.Dissipation
import CRNT.Theorems.DeficiencyZero.Toric
import CRNT.Theorems.DeficiencyZero.Characterization
import CRNT.Equilibria.ComplexBalanceStructure

/-!
# Complex-balanced systems are quasi-thermostatic

**Theorem (Horn–Jackson 1972).**  Suppose the mass-action system `(N, κ)` has a positive
complex-balanced equilibrium `x*`.  Then

* every positive steady state is complex balanced
  (`isComplexBalanced_of_positive_steadyState`), and
* a positive state `x` is a steady state iff `log x - log x* ∈ S^⊥`
  (`positiveSteadyState_iff_logRatio_mem_orthStoich`), i.e. the positive steady states form
  the toric set `{x* ∘ exp μ | μ ∈ S^⊥}` (Feinberg's *quasi-thermostatic* property).

Both follow from results already in the library: the entropy-dissipation identity
(`complexBalanced_of_dissipation_eq_zero`) and the log-ratio characterization of complex balance
(`logRatio_orthogonal_of_complexBalanced`, `complexBalanced_of_logRatio_orthogonal`).

Nothing here is an axiom or a `sorry`.
-/

namespace CRNT
namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Every positive steady state of a complex-balanced system is complex balanced.** -/
theorem isComplexBalanced_of_positive_steadyState (N : Network S) (κ : N.RateConstants)
    {x xstar : Concentration S} (hx : x.Positive) (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar) (hss : N.IsMassActionSteadyState κ x) :
    N.IsComplexBalanced κ x := by
  apply N.complexBalanced_of_dissipation_eq_zero κ hx hxs hcb
  apply Finset.sum_eq_zero
  intro s _
  rw [hss s, mul_zero]

/-- **Quasi-thermostatic property.** -/
theorem positiveSteadyState_iff_logRatio_mem_orthStoich (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    {x : Concentration S} (hx : x.Positive) :
    N.IsMassActionSteadyState κ x ↔
      (fun s => Real.log (x s) - Real.log (xstar s)) ∈ orthSum N.stoichSubspace := by
  have hwr := N.weaklyReversible_of_positive_complexBalanced κ hxs hcb
  constructor
  · intro hss
    exact N.logRatio_orthogonal_of_complexBalanced hwr κ hx hxs
      (N.isComplexBalanced_of_positive_steadyState κ hx hxs hcb hss) hcb
  · intro horth
    exact N.isMassActionSteadyState_of_complexBalanced κ
      (N.complexBalanced_of_logRatio_orthogonal κ hx hxs hcb horth)

/-- Positive steady states and positive complex-balanced states coincide once one positive
complex-balanced state exists. -/
theorem positiveSteadyState_iff_complexBalanced (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    {x : Concentration S} (hx : x.Positive) :
    N.IsMassActionSteadyState κ x ↔ N.IsComplexBalanced κ x :=
  ⟨N.isComplexBalanced_of_positive_steadyState κ hx hxs hcb,
    N.isMassActionSteadyState_of_complexBalanced κ⟩

end Network
end CRNT
