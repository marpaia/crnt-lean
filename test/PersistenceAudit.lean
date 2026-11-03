import CRNT.Dynamics.GlobalAttractorTheorem
import CRNT.Persistence.ComplexBalancedFloor

/-!
# Axiom audit of the persistence route to the Global Attractor Theorem

Every theorem of `CRNT/Persistence/` that the closure of the GAC residual rests on, and the GAC
chain itself, is pinned to `[propext, Classical.choice, Quot.sound]`.  Fast to run: it imports only
the GAC chain, not the whole of `CRNT`.
-/

/-- info: 'CRNT.Persistence.circulation_pairing_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Persistence.circulation_pairing_nonneg

/-- info: 'CRNT.Persistence.BTree.realized_of_isMin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Persistence.BTree.realized_of_isMin

/-- info: 'CRNT.Persistence.gap_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Persistence.gap_ge

/-- info: 'CRNT.Persistence.lfsGe_update' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Persistence.lfsGe_update

/-- info: 'CRNT.Persistence.build_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Persistence.build_spec

/-- info: 'CRNT.Persistence.walk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Persistence.walk

/-- info: 'CRNT.Persistence.level_validity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Persistence.level_validity

/-- info: 'CRNT.Persistence.sort_reduce' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Persistence.sort_reduce

/-- info: 'CRNT.Persistence.sorted_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Persistence.sorted_valid

/-- info: 'CRNT.Persistence.exists_zsh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Persistence.exists_zsh

/-- info: 'CRNT.Network.dot_massActionField_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.dot_massActionField_nonneg

/-- info: 'CRNT.Network.complexBalanced_forward_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.complexBalanced_forward_floor

/-- info: 'CRNT.Network.exists_positive_omegaPoint_of_highCodimension_siphonFace_nonVertex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.exists_positive_omegaPoint_of_highCodimension_siphonFace_nonVertex

/-- info: 'CRNT.Network.complexBalanced_genuinePermanent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.complexBalanced_genuinePermanent

/-- info: 'CRNT.Network.complexBalanced_globalAttractor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.complexBalanced_globalAttractor
