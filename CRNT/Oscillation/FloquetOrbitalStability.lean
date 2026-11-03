import CRNT.Oscillation.Floquet
import CRNT.Oscillation.ReturnMap
import CRNT.Oscillation.ReturnMapContraction
import CRNT.Dynamics.FlowSmoothDependence
import Mathlib.Analysis.Normed.Algebra.Spectrum

/-!
# Floquet multipliers and nonlinear orbital attraction

This module exposes the nonlinear orbital-stability target to the oscillation kernel bundle. The
transverse-section construction, spectral-radius/contraction argument, and tube-basin step are not
proved in the current source tree, so the result remains an explicit input instead of an
unconditional theorem.
-/

namespace CRNT
namespace Network

open Filter Topology

/-- The transverse-section, contraction, and flow-interpolation route has not been constructed
in this checkout. Keep the required nonlinear theorem as an explicit input to the kernel bundle. -/
abbrev FloquetOrbitalStabilityObligation : Prop := FloquetOrbitalStabilityTarget

/-- Compatibility spelling for the previous tube-level obligation. It now names the full
non-vacuous orbital-stability target, rather than an obligation over an undeclared section package. -/
abbrev FloquetTubeObligation : Prop := FloquetOrbitalStabilityObligation

/-- The completed nonlinear theorem is obtained from its explicit mathematical obligation. -/
theorem floquetOrbitalStability_of_tube
    (h : FloquetTubeObligation) : FloquetOrbitalStabilityTarget := h

/-- Descriptive spelling for callers that supply the actual target directly. -/
theorem floquetOrbitalStability_of_obligation
    (h : FloquetOrbitalStabilityObligation) : FloquetOrbitalStabilityTarget := h

end Network
end CRNT
