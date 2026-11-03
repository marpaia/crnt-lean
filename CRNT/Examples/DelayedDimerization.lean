import CRNT.Dynamics.MassActionDelayExistence
import CRNT.Stochastic.ConservativeLLN

/-! # Global delayed existence for the nonlinear dimerization network

The reversible bimolecular network `2X ⇌ Y` has the strictly positive conserved weight
`(1, 2)`. It therefore satisfies the global continuation theorem for arbitrary
reaction-specific nonnegative delays and every continuous nonnegative history.
-/

namespace CRNT
namespace Examples
namespace Dimerization

open Network

/-- The nonlinear conservative network `2X ⇌ Y` has a global delayed solution for every
nonnegative reaction-specific delay assignment and every continuous nonnegative history. -/
theorem delayed_global_exists (τ : net.R → ℝ) (hτ : ∀ r, 0 ≤ τ r)
    (φ : ℝ → Concentration (Fin 2)) (hφ : Continuous φ)
    (hφnonneg : ∀ t ≤ 0, ∀ s, 0 ≤ φ t s) :
    ∃ x : ℝ → Concentration (Fin 2), (∀ t ≤ 0, x t = φ t) ∧
      ∀ T : ℝ, 0 ≤ T → ContinuousOn x (Set.Icc 0 T) ∧
        ∀ t ∈ Set.Icc 0 T,
          HasDerivWithinAt x (net.delayField κ τ x t) (Set.Icc 0 T) t := by
  exact net.massActionDelay_global_exists_of_positive_conservation κ τ hτ w w_inv w_pos
    φ hφ hφnonneg

#print axioms CRNT.Examples.Dimerization.delayed_global_exists

end Dimerization
end Examples
end CRNT
