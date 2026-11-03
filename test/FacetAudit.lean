import CRNT.Persistence.DGCriticalPersistence
import CRNT.Persistence.BoundedWRPersistence
import CRNT.Examples.FacetRepulsionPair

/-! Axiom audit: Anderson–Shiu facet repulsion (D10) and paper-notion siphon persistence (D11). -/

/-- info: 'CRNT.Network.orbitClosure_positive_of_hasNoDGCriticalSiphon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.orbitClosure_positive_of_hasNoDGCriticalSiphon

/-- info: 'CRNT.Network.hasNoDGCriticalSiphon_of_weaklyReversible_hasNoSelfReplicableSiphon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.hasNoDGCriticalSiphon_of_weaklyReversible_hasNoSelfReplicableSiphon

/-- info: 'CRNT.Network.exists_minimalDGCriticalSiphon_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.exists_minimalDGCriticalSiphon_subset

/-- info: 'CRNT.Network.omegaPoint_positive_of_weaklyReversible_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.omegaPoint_positive_of_weaklyReversible_bounded

/-- info: 'CRNT.Network.exists_facet_coefficient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.exists_facet_coefficient

/-- info: 'CRNT.Network.exists_dominating_reaction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.exists_dominating_reaction

/-- info: 'CRNT.Network.facet_repelling_of_weaklyReversible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.facet_repelling_of_weaklyReversible

/-- info: 'CRNT.Examples.ReversiblePair.facet_repelling_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Examples.ReversiblePair.facet_repelling_pair
