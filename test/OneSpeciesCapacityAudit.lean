import CRNT.Multistationarity.OneSpeciesCapacity
import CRNT.Multistationarity.CapacityCharacterization
import CRNT.Extensions.DelayMassAction
import CRNT.Multistationarity.OneSpeciesNecessity

#print axioms CRNT.Network.oneSpecies_multistationary_of_upDownUp

namespace OneSpeciesCapacityAudit
open CRNT

/-- `0 → A`, `2A → A`, `3A → 4A`: arrows up, down, up at reactant coefficients `0 < 2 < 3`. -/
def net : Network (Fin 1) :=
  ⟨Fin 3, inferInstance, inferInstance, fun r =>
    if r = 0 then ⟨![0], ![1]⟩ else if r = 1 then ⟨![2], ![1]⟩ else ⟨![3], ![4]⟩⟩

/-- Non-vacuity: this network is multistationary for suitable rate constants. -/
example : ∃ (κ : net.RateConstants) (x z : Concentration (Fin 1)), x.Positive ∧ z.Positive ∧
    x ≠ z ∧ x - z ∈ net.stoichSubspace ∧ net.IsMassActionSteadyState κ x ∧
      net.IsMassActionSteadyState κ z :=
  net.oneSpecies_multistationary_of_upDownUp ((0 : Fin 3) : net.R) ((1 : Fin 3) : net.R)
    ((2 : Fin 3) : net.R) (by decide) (by decide)
    (by simp [net, Network.reactionVector]) (by simp [net, Network.reactionVector])
    (show (0 : ℝ) < ((4 : ℕ) : ℝ) - ((3 : ℕ) : ℝ) by norm_num)

end OneSpeciesCapacityAudit

#print axioms CRNT.Network.hasMultistationarityCapacity_iff_flux_sign
#print axioms CRNT.Network.const_isDelaySolution_iff
#print axioms CRNT.Network.delayConservedQuantity_const
#print axioms CRNT.Polynomial.no_two_pos_roots_of_no_alternation
#print axioms CRNT.Network.oneSpecies_unique_positiveSteadyState_of_no_pattern
#print axioms CRNT.Network.oneSpecies_multistationary_of_downUpDown
#print axioms CRNT.Network.oneSpecies_nondegenerate_multistationary_iff
