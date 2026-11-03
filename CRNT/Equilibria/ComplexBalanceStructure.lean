import CRNT.Equilibria.ComplexBalanced
import CRNT.Dynamics.MassActionAlgebra
import CRNT.Deficiency.Drainage

/-!
# Structural consequences of positive complex balance

A positive complex-balanced state gives a strictly positive vector in the kernel of the
kinetic Laplacian `A_k`: its complex-monomial vector.  The drainage theorem then forces
weak reversibility.  This is the classical converse structural fact complementing the
deficiency-zero theorem:

`positive complex balance  ⟹  weak reversibility`.

The proof is completely independent of deficiency.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- At a positive concentration every complex monomial is strictly positive. -/
theorem complexMonomialVector_pos (N : Network S) {x : Concentration S}
    (hx : x.Positive) : ∀ c : N.ComplexIdx, 0 < N.complexMonomialVector x c := by
  intro c
  exact Complex.massActionMonomial_pos hx c.1

/-- Complex balance is exactly membership of the positive complex-monomial vector in the
kinetic kernel. -/
theorem kineticMap_complexMonomial_eq_zero_of_complexBalanced
    (N : Network S) (κ : N.RateConstants) {x : Concentration S}
    (hcb : N.IsComplexBalanced κ x) :
    N.kineticMap κ (N.complexMonomialVector x) = 0 := by
  funext c
  rw [N.kineticMap_complexMonomial_apply κ x c]
  exact sub_eq_zero.mpr (hcb c.1 c.2)

/-- **Positive complex balance forces weak reversibility.** -/
theorem weaklyReversible_of_positive_complexBalanced
    (N : Network S) (κ : N.RateConstants) {x : Concentration S}
    (hx : x.Positive) (hcb : N.IsComplexBalanced κ x) :
    N.WeaklyReversible := by
  exact N.weaklyReversible_of_exists_pos_kernelVector κ
    (N.complexMonomialVector_pos hx)
    (N.kineticMap_complexMonomial_eq_zero_of_complexBalanced κ hcb)

/-- A network that is not weakly reversible has no positive complex-balanced state for
any positive rate constants. -/
theorem no_positive_complexBalanced_of_not_weaklyReversible
    (N : Network S) (hN : ¬ N.WeaklyReversible) (κ : N.RateConstants) :
    ¬ ∃ x : Concentration S, x.Positive ∧ N.IsComplexBalanced κ x := by
  rintro ⟨x, hx, hcb⟩
  exact hN (N.weaklyReversible_of_positive_complexBalanced κ hx hcb)

/-- Existence of a positive complex-balanced state is equivalent, on the structural side,
to existence of a strictly positive kinetic-kernel vector that happens to lie in the
image of the complex-monomial map. -/
theorem exists_positive_complexBalanced_iff_exists_positive_monomial_kernel
    (N : Network S) (κ : N.RateConstants) :
    (∃ x : Concentration S, x.Positive ∧ N.IsComplexBalanced κ x) ↔
      ∃ x : Concentration S,
        x.Positive ∧ N.kineticMap κ (N.complexMonomialVector x) = 0 := by
  constructor
  · rintro ⟨x, hx, hcb⟩
    exact ⟨x, hx, N.kineticMap_complexMonomial_eq_zero_of_complexBalanced κ hcb⟩
  · rintro ⟨x, hx, hker⟩
    refine ⟨x, hx, ?_⟩
    intro c hc
    have h := congrFun hker ⟨c, hc⟩
    rw [N.kineticMap_complexMonomial_apply κ x ⟨c, hc⟩] at h
    exact sub_eq_zero.mp h

end Network
end CRNT
