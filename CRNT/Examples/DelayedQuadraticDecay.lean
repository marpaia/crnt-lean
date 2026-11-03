import CRNT.Dynamics.MassActionDelayExistence

/-! # A nonconservative nonlinear example of delayed global existence

For `2X → X`, the strictly positive weight `w(X)=1` strictly decreases along the reaction.
The weighted delayed inventory therefore decreases, yet still bounds the concentration and yields
global existence for every nonnegative reaction delay and continuous nonnegative history.
-/

namespace CRNT
namespace Examples
namespace DelayedQuadraticDecay

open Network

/-- The quadratic reaction `2X → X`, whose stoichiometric change is strictly negative. -/
abbrev net : Network (Fin 1) :=
  ⟨Fin 1, inferInstance, inferInstance, fun _ => ⟨![2], ![1]⟩⟩

def κ : RateConstants net := ⟨fun _ => 1, fun _ => one_pos⟩

/-- The positive species weight; it is strictly lost by the reaction `2X → X`. -/
def w : Fin 1 → ℝ := fun _ => 1

theorem strict_weight_loss (r : net.R) :
    ∑ s, w s * ((net.reaction r).target s : ℝ) <
      ∑ s, w s * ((net.reaction r).source s : ℝ) := by
  fin_cases r
  norm_num [w]

/-- The nonconservative network `2X → X` has a global delayed solution from every continuous
nonnegative history, for every nonnegative delay. -/
theorem delayed_global_exists (τ : net.R → ℝ) (hτ : ∀ r, 0 ≤ τ r)
    (φ : ℝ → Concentration (Fin 1)) (hφ : Continuous φ)
    (hφnonneg : ∀ t ≤ 0, ∀ s, 0 ≤ φ t s) :
    ∃ x : ℝ → Concentration (Fin 1), (∀ t ≤ 0, x t = φ t) ∧
      ∀ T : ℝ, 0 ≤ T → ContinuousOn x (Set.Icc 0 T) ∧
        ∀ t ∈ Set.Icc 0 T,
          HasDerivWithinAt x (net.delayField κ τ x t) (Set.Icc 0 T) t := by
  exact net.massActionDelay_global_exists_of_weighted_subconservation κ τ hτ w
    (fun r => (strict_weight_loss r).le) (by intro s; fin_cases s; norm_num [w])
    φ hφ hφnonneg

#print axioms CRNT.Examples.DelayedQuadraticDecay.strict_weight_loss
#print axioms CRNT.Examples.DelayedQuadraticDecay.delayed_global_exists

end DelayedQuadraticDecay
end Examples
end CRNT
