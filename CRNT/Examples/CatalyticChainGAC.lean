import CRNT.Examples.CatalyticChain
import CRNT.Dynamics.GACLowRank
import CRNT.Theorems.DeficiencyZero.Existence

/-!
# The global attractor property for the catalytic chain, axiom-clean

`CRNT.Examples.CatalyticChain` is the network `A + C ⇌ 2C ⇌ B + C` (weakly reversible,
deficiency zero, stoichiometric rank two).  Its siphon `{B, C}` has a codimension-two face —
the configuration of the residual obligation (`CRNT.Examples.CodimTwoFaceModel` uses this network
to show the residual needs the orbit-ODE hypothesis).

Through `complexBalanced_trajectory_converges_of_stoichRank_le_two`, the global attractor
property of this network no longer depends on Hole A: for every choice of rate constants there is
a positive complex-balanced equilibrium, and every genuine positive trajectory in its class
converges to it.

Nothing here is an axiom or a `sorry`.
-/

namespace CRNT.Examples.CatalyticChain

/-- **Global attractor property of the catalytic chain** (axiom-clean). -/
theorem globalAttractor (κ : N.RateConstants) :
    ∃ xstar : Concentration (Fin 3), xstar.Positive ∧ N.IsComplexBalanced κ xstar ∧
      N.PositiveClassTrajectoryConverges κ xstar := by
  obtain ⟨xstar, hxs, hcb⟩ := N.exists_isComplexBalanced weaklyReversible deficiencyZero κ
  exact ⟨xstar, hxs, hcb,
    N.complexBalanced_trajectory_converges_of_stoichRank_le_two κ hxs hcb (by rw [stoichRank_eq])⟩

end CRNT.Examples.CatalyticChain
