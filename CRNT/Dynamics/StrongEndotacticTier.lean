import CRNT.Dynamics.TierDirectionExistence
import CRNT.Dynamics.GlobalPersistenceFrontier

/-!
# Strongly endotactic networks are exactly the tier-descending networks

With the finite-dimensional input `everyTransversalTierDirectionSystemFeasible` proved, the
repository's reduction gives the tier characterization unconditionally:
`StronglyEndotacticStd ↔ TierDescending` (Anderson–Cappelletti–Kim–Nguyen 2020, tier structure of
strongly endotactic networks).  The permanence step `TierDescendingPermanenceClaim` remains a named
claim.

Nothing here is an axiom or a `sorry`.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- `TierDirectionSystemFeasibilityClaim` holds for every network. -/
theorem tierDirectionSystemFeasibilityClaim (N : Network S) : N.TierDirectionSystemFeasibilityClaim :=
  N.everyTransversalTierDirectionSystemFeasible

/-- **Tier characterization of strong endotacticity.** -/
theorem stronglyEndotacticStd_iff_tierDescending (N : Network S) :
    N.StronglyEndotacticStd ↔ N.TierDescending :=
  N.stronglyEndotacticStd_iff_tierDescending_of_forwardClaim
    (N.strongEndotacticTierDescending_of_systemFeasibility N.tierDirectionSystemFeasibilityClaim)

end Network
end CRNT
