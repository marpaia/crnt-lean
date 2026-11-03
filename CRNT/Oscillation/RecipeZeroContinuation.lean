import CRNT.Oscillation.RecipeZero

/-!
# Concrete smooth continuation for parameter-rich Recipe 0

`RecipeZeroCertificate` already contains the complete finite symbolic-Jacobian path: admissible
stable/unstable reactivities, a rank-sized principal block, and nonsingularity of that block on the
whole straight interpolation.  `SupportsSmoothReactivityPaths` realizes the interpolation by one
coherent smooth kinetic family at any chosen positive state.

This file performs that realization explicitly.  The only theorem left after this construction is
the nonlinear global-Hopf implication for the resulting smooth kinetic continuation.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]
variable {N : Network S}

/-- Smooth kinetic realization of one Recipe-0 certificate at a fixed positive state. -/
structure SmoothRecipeZeroContinuation
    (C : RecipeZeroCertificate N)
    (F : N.SteadyStateParameterRichFamily)
    (x : Concentration S) : Type where
  positiveState : x.Positive
  realization : N.SmoothLinearReactivityRealization F x C.stableR C.unstableR

namespace RecipeZeroCertificate

/-- Smooth-path support realizes a Recipe-0 path at every prescribed positive state. -/
theorem exists_smoothContinuation
    (C : RecipeZeroCertificate N)
    (F : N.SteadyStateParameterRichFamily)
    (hpaths : N.SupportsSmoothReactivityPaths F)
    (x : Concentration S) (hx : x.Positive) :
    Nonempty (SmoothRecipeZeroContinuation C F x) := by
  obtain ⟨P⟩ := hpaths x hx C.stableR C.unstableR
    C.stableR_admissible C.unstableR_admissible
  exact ⟨{ positiveState := hx, realization := P }⟩

end RecipeZeroCertificate

/-- Exact nonlinear theorem after the Recipe-0 path itself has been realized. -/
def RecipeZeroSmoothContinuationTarget : Prop :=
  ∀ {T : Type} [DecidableEq T] [Fintype T]
    (N : Network T) (F : N.SteadyStateParameterRichFamily)
    (C : RecipeZeroCertificate N) (x : Concentration T)
    (P : SmoothRecipeZeroContinuation C F x),
      N.ParameterRichOscillatoryCapacity F

/-- The concrete smooth-continuation theorem implies the older broad Recipe-0 realization target. -/
theorem parameterRichRecipeZeroRealization_of_smoothContinuation
    (hHopf : RecipeZeroSmoothContinuationTarget) :
    ParameterRichRecipeZeroRealizationTarget := by
  intro T _ _ N F hpaths _hcons hC
  obtain ⟨C⟩ := hC
  let x : Concentration T := fun _ => 1
  have hx : x.Positive := by intro i; exact zero_lt_one
  obtain ⟨P⟩ := C.exists_smoothContinuation F hpaths x hx
  exact hHopf N F C x P

end Network
end CRNT
