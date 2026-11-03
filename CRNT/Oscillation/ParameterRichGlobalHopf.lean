import CRNT.Oscillation.ParameterRichDHopfContinuation
import CRNT.Oscillation.RecipeZeroContinuation

/-!
# Recipe 0 and parameter-rich D-Hopf targets

The reduced-kinetic completion and nonlinear Hopf implications remain external theorem targets. This
module forwards explicit certificates into the existing compatibility interfaces.
-/

namespace CRNT
namespace Network

/-- Forward the explicit nonlinear result for a realized Recipe-0 continuation. -/
theorem parameterRichRecipeZeroRealization_of_target
    (h : RecipeZeroSmoothContinuationTarget) :
    ParameterRichRecipeZeroRealizationTarget :=
  parameterRichRecipeZeroRealization_of_smoothContinuation h

/-- Forward the explicit nonlinear result for a realized parameter-rich D-Hopf continuation. -/
theorem parameterRichDHopfContinuation_of_target
    (h : ParameterRichDHopfContinuationTarget) :
    ParameterRichDHopfContinuationTarget := h

end Network

end CRNT
