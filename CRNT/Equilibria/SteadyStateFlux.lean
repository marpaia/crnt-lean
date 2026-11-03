import CRNT.Equilibria.SteadyState
import CRNT.Flux.Cone

/-!
# Positive steady states induce positive stationary fluxes

At a positive mass-action steady state, the reaction-rate vector

`v_r = k_r x^{y_r}`

is strictly positive and satisfies `S v = 0`.  Hence every positive steady state gives a
strictly positive point of the CRNT flux cone and in particular proves network
consistency.  This elementary bridge is useful in deficiency and weak-reversibility
arguments.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Reaction-rate vector at a concentration. -/
def reactionRateVector (N : Network S) (κ : N.RateConstants)
    (x : Concentration S) : N.R → ℝ :=
  fun r => N.massActionRate κ r x

/-- At positive concentration all reaction-rate coordinates are strictly positive. -/
theorem reactionRateVector_positive (N : Network S) (κ : N.RateConstants)
    {x : Concentration S} (hx : x.Positive) :
    N.IsPositiveFlux (N.reactionRateVector κ x) := by
  intro r
  exact N.massActionRate_pos κ r hx

/-- Steady state is exactly stationarity of the reaction-rate vector. -/
theorem isMassActionSteadyState_iff_rateVector_stationary
    (N : Network S) (κ : N.RateConstants) (x : Concentration S) :
    N.IsMassActionSteadyState κ x ↔
      N.IsStationaryFlux (N.reactionRateVector κ x) := by
  constructor
  · intro hss
    funext s
    have hs := hss s
    simpa [reactionRateVector, IsStationaryFlux, stoichMap_apply,
      massActionVectorField] using hs
  · intro hflux s
    have hs := congrFun hflux s
    simpa [reactionRateVector, IsStationaryFlux, stoichMap_apply,
      massActionVectorField] using hs

/-- Positive steady states produce strictly positive flux-cone points. -/
theorem positiveSteadyState_gives_positiveFluxCone
    (N : Network S) (κ : N.RateConstants)
    {x : Concentration S} (hx : x.Positive)
    (hss : N.IsMassActionSteadyState κ x) :
    N.reactionRateVector κ x ∈ N.FluxCone ∧
      N.IsPositiveFlux (N.reactionRateVector κ x) := by
  refine ⟨?_, N.reactionRateVector_positive κ hx⟩
  exact ⟨fun r => (N.massActionRate_pos κ r hx).le,
    (N.isMassActionSteadyState_iff_rateVector_stationary κ x).1 hss⟩

/-- **Positive steady-state existence implies consistency.** -/
theorem isConsistent_of_exists_positive_massActionSteadyState
    (N : Network S)
    (h : ∃ κ : N.RateConstants, ∃ x : Concentration S,
      x.Positive ∧ N.IsMassActionSteadyState κ x) :
    N.IsConsistent := by
  rcases h with ⟨κ, x, hx, hss⟩
  rw [N.isConsistent_iff_exists_positive_fluxCone]
  exact ⟨N.reactionRateVector κ x,
    (N.positiveSteadyState_gives_positiveFluxCone κ hx hss).1,
    (N.positiveSteadyState_gives_positiveFluxCone κ hx hss).2⟩

/-- Fixed-rate version. -/
theorem isConsistent_of_positive_massActionSteadyState
    (N : Network S) (κ : N.RateConstants)
    {x : Concentration S} (hx : x.Positive)
    (hss : N.IsMassActionSteadyState κ x) :
    N.IsConsistent := by
  exact N.isConsistent_of_exists_positive_massActionSteadyState
    ⟨κ, x, hx, hss⟩

end Network
end CRNT
