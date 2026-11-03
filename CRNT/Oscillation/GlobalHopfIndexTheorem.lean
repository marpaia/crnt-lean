import CRNT.Oscillation.GlobalHopfIndex
import CRNT.Dynamics.HopfRealizes
import CRNT.Multistationarity.DegreeHomotopyInvariant

/-!
# Analytic global Hopf target

The finite-dimensional unstable-index package and the exact nonlinear conclusion live in
`GlobalHopfIndex.lean`. The missing Fiedler/Alexander--Yorke argument uses analytic approximation,
local Hopf degree, spectral-flow additivity, and periodic-orbit compactness results that are not
proved in this checkout. This module exposes that conclusion as an explicit obligation and adapts it
to the historical Fiedler interface.
-/

namespace CRNT

/-- The analytic global-Hopf theorem remains an explicit kernel input. -/
abbrev AnalyticGlobalHopfIndexObligation : Prop := AnalyticGlobalHopfIndexTarget

/-- Forward the supplied analytic index theorem to the exact target consumed downstream. -/
theorem analyticGlobalHopfIndex
    (hIndex : AnalyticGlobalHopfIndexObligation) : AnalyticGlobalHopfIndexTarget := hIndex

/-- The index-form global Hopf theorem implies the historical Fiedler interface. -/
theorem fiedlerAnalyticGlobalHopf_of_target
    (hIndex : AnalyticGlobalHopfIndexObligation) : FiedlerAnalyticGlobalHopfTarget :=
  fiedlerAnalyticGlobalHopf_of_index hIndex

end CRNT
