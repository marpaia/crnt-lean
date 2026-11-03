import CRNT.Oscillation.GlobalHopfIndexTheorem
import CRNT.Oscillation.SpectralOpenness

/-!
# Smooth global Hopf targets

The passage from smooth to analytic continuation and the compactness step are not yet proved. This
module makes both the unrestricted smooth-family conclusion and the stronger local-radius conclusion
explicit inputs for their CRN consumers.
-/

namespace CRNT

/-- A periodic witness controlled in distance from the equilibrium branch. This is the correct
coordinate-free output for reduced stoichiometric dynamics. -/
structure LocalContinuationPeriodicWitness
    {I : Type} [DecidableEq I] [Fintype I]
    (C : SmoothEquilibriumContinuation I) (radius : ℝ) : Type where
  parameter : ℝ
  parameter_mem : parameter ∈ Set.Icc (0 : ℝ) 1
  trajectory : PeriodicTrajectory (C.field parameter)
  close : ∀ t, ‖trajectory.orbit t - C.equilibrium parameter‖ < radius

/-- Smooth global-Hopf conclusion for every continuation in the Fiedler setup. -/
def SmoothGlobalHopfTarget : Prop :=
  ∀ {I : Type} [DecidableEq I] [Fintype I]
    (C : SmoothEquilibriumContinuation I),
    Nonempty (PositiveContinuationPeriodicWitness C)

/-- Stronger local conclusion required to keep the periodic trajectory inside a prescribed
positive stoichiometric chart. -/
def SmoothGlobalHopfLocalTarget : Prop :=
  ∀ {I : Type} [DecidableEq I] [Fintype I]
    (C : SmoothEquilibriumContinuation I) (radius : ℝ),
    0 < radius → Nonempty (LocalContinuationPeriodicWitness C radius)

/-- Forward an explicit smooth global-Hopf certificate. -/
theorem smoothGlobalHopf
    (hHopf : SmoothGlobalHopfTarget)
    {I : Type} [DecidableEq I] [Fintype I]
    (C : SmoothEquilibriumContinuation I) :
    Nonempty (PositiveContinuationPeriodicWitness C) := hHopf C

/-- Forward an explicit local smooth global-Hopf certificate. -/
theorem smoothGlobalHopf_local
    (hLocal : SmoothGlobalHopfLocalTarget)
    {I : Type} [DecidableEq I] [Fintype I]
    (C : SmoothEquilibriumContinuation I)
    {radius : ℝ} (hr : 0 < radius) :
    Nonempty (LocalContinuationPeriodicWitness C radius) := hLocal C radius hr

end CRNT
