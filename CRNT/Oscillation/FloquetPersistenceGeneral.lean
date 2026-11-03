import CRNT.Oscillation.FloquetOrbitalStability
import CRNT.Oscillation.ReturnMapFamilyPersistence
import CRNT.Oscillation.DependentReaction
import CRNT.Oscillation.SpectralOpenness

/-!
# Dependent-reaction periodic-orbit persistence targets

The codimension-one parameterized Poincare construction, monodromy continuity, and stability-open
arguments are not completed here. Their end-to-end conclusions remain explicit targets for the
oscillation kernel bundle.
-/

namespace CRNT
namespace Network

/-- Universal form of the nondegenerate persistence target over finite species types. -/
def NondegenerateDependentReactionPersistenceAllTypesTarget : Prop :=
  ∀ {S : Type} [DecidableEq S] [Fintype S],
    Network.NondegenerateDependentReactionPersistenceTarget (S := S)

/-- Universal form of the stable persistence target over finite species types. -/
def StableDependentReactionPersistenceAllTypesTarget : Prop :=
  ∀ {S : Type} [DecidableEq S] [Fintype S],
    Network.StableDependentReactionPersistenceTarget (S := S)

/-- Forward an explicit nondegenerate dependent-reaction persistence certificate. -/
theorem nondegenerateDependentReactionPersistence_of_target
    (h : NondegenerateDependentReactionPersistenceAllTypesTarget) :
    NondegenerateDependentReactionPersistenceAllTypesTarget := h

/-- Forward an explicit linearly stable dependent-reaction persistence certificate. -/
theorem stableDependentReactionPersistence_of_target
    (h : StableDependentReactionPersistenceAllTypesTarget) :
    StableDependentReactionPersistenceAllTypesTarget := h

end Network
end CRNT
