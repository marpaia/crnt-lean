import CRNT.Dynamics.HighCodimensionSiphonFace
import CRNT.Dynamics.FaceDirectionCone
import CRNT.Dynamics.SiphonDimensionDescent
import CRNT.Dynamics.ComplexBalanceStoichFanInclusion

/-!
# Pins for the Hole-A audit

The fork adjudication is consolidated by `infra-scaffold-crnt` in
`CRNT/Dynamics/UpperRegionFloorRefutation.lean`; this audit's copy was reduced to a corollary and
then dropped as a duplicate. The pinned facts below are the ones this audit verified directly and
that no other branch claims.

`Network.comparableGrowthDescent_iff_omegaPointPositive` (SiphonDimensionDescent.lean:368) is the
route-selection fact -- the descent fallback the hole's docstring names is the goal itself. It is
already in the tree and needs no pin of its own; the pin exists so a regression in it is caught.
-/

#print axioms CRNT.Network.comparableGrowthDescent_iff_omegaPointPositive
#print axioms CRNT.Network.descendStep_iff_omegaPointPositive_of_cardMinimal
#print axioms CRNT.Network.hsep_fails_of_boundaryPoint_mem_sublevel
#print axioms CRNT.Network.barrier_le_of_mem_omegaLimit
#print axioms CRNT.Network.not_persistentFrom_of_mem_omegaLimit_notPositive
#print axioms CRNT.Network.exists_positive_omegaPoint_of_upperRegion
#print axioms CRNT.Network.exists_positive_omegaPoint_of_faceRelevantCore
#print axioms CRNT.Network.isInclusionSolutionOn_massAction_relativeSourceOrder
