import CRNT
import CRNTFrontier

/-!
# Frontier theorem dependency audit

This file pins the current global-attraction, SR-graph, and Floquet endpoints.
`test.FrontierAudit` separately pins the conditional oscillation bundle constructors. Both run
under `lake test`; auditing a conditional constructor does not discharge its input hypotheses.

## Why the incomplete results are pinned too

Both former holes are now pinned **clean**.  If a `sorryAx` reappears in either chain, this file
fails and forces the ledger and handoffs to be updated in the same commit.

Regenerate expectations by running the corresponding `#print axioms` and pasting the output.
-/

/-! ## Closed: the Global Attractor Conjecture

The former residual `exists_positive_omegaPoint_of_highCodimension_siphonFace_nonVertex`
(`CRNT/Dynamics/HighCodimensionSiphonFace.lean`) is proved from
`Network.complexBalanced_forward_floor` (`CRNT/Persistence/ComplexBalancedFloor.lean`).  The whole
chain, up to `complexBalanced_globalAttractor`, is pinned clean.  See `HANDOFF_gac_closed.md`. -/

/-- info: 'CRNT.Network.exists_positive_omegaPoint_of_highCodimension_siphonFace_nonVertex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.exists_positive_omegaPoint_of_highCodimension_siphonFace_nonVertex

/-- info: 'CRNT.Network.false_of_vertex_omegaPoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.false_of_vertex_omegaPoint

/-- info: 'CRNT.Network.exists_positive_omegaPoint_of_highCodimension_siphonFace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.exists_positive_omegaPoint_of_highCodimension_siphonFace

/-- info: 'CRNT.Network.complexBalanced_genuinePermanent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.complexBalanced_genuinePermanent

/-- info: 'CRNT.Network.complexBalanced_permanent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.complexBalanced_permanent

/-- info: 'CRNT.Network.complexBalanced_globalAttractor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.complexBalanced_globalAttractor

/-! ## Closed: the Shinar--Feinberg true-SR criterion

`stronglyConcordant_fullyOpen_of_trueSRCriterion` is now proved by the Banaji--Craciun
determinant argument (`CRNT/Multistationarity/BCFullyOpen.lean`), so it and its consumers must
audit clean.  `test/BanajiCraciunAudit.lean` pins the route itself. -/

/-- info: 'CRNT.Network.stronglyConcordant_fullyOpen_of_trueSRCriterion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.stronglyConcordant_fullyOpen_of_trueSRCriterion

/-- info: 'CRNT.Network.stronglyConcordant_of_trueSRCriterion_of_weaklyNormal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.stronglyConcordant_of_trueSRCriterion_of_weaklyNormal

/-- info: 'CRNT.Network.injective_of_trueSRCriterion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.injective_of_trueSRCriterion

/-! ## Clean frontier endpoints

The tube-based Floquet result must retain only the allowed axioms. The general stability and
inheritance constructors still consume explicit targets, audited in `test.FrontierAudit`. -/

/-- info: 'CRNT.Network.floquetOrbitalStability_of_tube' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.floquetOrbitalStability_of_tube

/-! ## The GAC reduction chain must stay clean

If any of these acquires `sorryAx`, the reduction has been short-circuited through the open
obligation rather than proved. -/

/-- info: 'CRNT.Network.exists_positive_omegaPoint_of_blueprintData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.exists_positive_omegaPoint_of_blueprintData

/-- info: 'CRNT.Network.orbit_pos_forward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.orbit_pos_forward

/-- info: 'CRNT.Network.stoichCompatible_of_forward_solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.stoichCompatible_of_forward_solution

/-- info: 'CRNT.Network.highCodimension_of_not_facet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.highCodimension_of_not_facet

/-- info: 'CRNT.PolyhedralBarrier.minMaxBarrier_le_of_local_descent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.PolyhedralBarrier.minMaxBarrier_le_of_local_descent

/-- info: 'CRNT.ConvexBarrierObstruction.not_exists_weights_vector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.ConvexBarrierObstruction.not_exists_weights_vector
