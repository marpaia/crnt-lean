import CRNT.Persistence.ConservativePersistence
import CRNT.Examples.ConservativeNonPersistent
import CRNT.Persistence.VariableRateFloor

/-! Axiom audit: weakly reversible persistence (bounded trajectories; conservative networks). -/

/-- info: 'CRNT.Persistence.cut_pairing_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Persistence.cut_pairing_nonneg

/-- info: 'CRNT.Persistence.exists_crossing_of_reflTransGen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Persistence.exists_crossing_of_reflTransGen

/-- info: 'CRNT.Network.dot_massActionField_nonneg_of_weaklyReversible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.dot_massActionField_nonneg_of_weaklyReversible

/-- info: 'CRNT.Network.exists_slack_weaklyReversible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.exists_slack_weaklyReversible

/-- info: 'CRNT.Network.weaklyReversible_forward_floor_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.weaklyReversible_forward_floor_uniform

/-- info: 'CRNT.Network.weaklyReversible_forward_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.weaklyReversible_forward_floor

/-- info: 'CRNT.Network.orbit_pos_forward_of_bdd_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.orbit_pos_forward_of_bdd_nonneg

/-- info: 'CRNT.Network.conservative_forward_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.conservative_forward_bound

/-- info: 'CRNT.Network.weaklyReversible_conservative_persistentFrom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.weaklyReversible_conservative_persistentFrom

/-- info: 'CRNT.Network.weaklyReversible_conservative_structurallyPersistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.weaklyReversible_conservative_structurallyPersistent

/-- info: 'CRNT.Network.persistenceConjectureStrong_of_conservative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.persistenceConjectureStrong_of_conservative

/-- info: 'CRNT.Network.persistenceConjecture_of_conservative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.persistenceConjecture_of_conservative

/-- info: 'CRNT.Examples.Minimal.isConservative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Examples.Minimal.isConservative

/-- info: 'CRNT.Examples.Minimal.not_persistentFrom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Examples.Minimal.not_persistentFrom

/-- info: 'CRNT.Examples.Minimal.not_structurallyPersistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Examples.Minimal.not_structurallyPersistent

/-- info: 'CRNT.Network.exists_field_lower_bound_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.exists_field_lower_bound_uniform

/-- info: 'CRNT.Network.exists_slack_varK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.exists_slack_varK

/-- info: 'CRNT.Network.orbit_pos_forward_varK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.orbit_pos_forward_varK

/-- info: 'CRNT.Network.sub_mem_stoichSubspace_of_solution_varK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.sub_mem_stoichSubspace_of_solution_varK

/-- info: 'CRNT.Network.weaklyReversible_forward_floor_varK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.weaklyReversible_forward_floor_varK

/-- info: 'CRNT.Network.weaklyReversible_conservative_confined_varK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.weaklyReversible_conservative_confined_varK

-- non-vacuity: weak reversibility cannot be dropped from the conservative theorem
example : CRNT.Examples.Minimal.N.IsConservative ∧ ¬ CRNT.Examples.Minimal.N.WeaklyReversible ∧
    ¬ CRNT.Examples.Minimal.N.StructurallyPersistent :=
  ⟨CRNT.Examples.Minimal.isConservative, CRNT.Examples.Minimal.not_weaklyReversible,
    CRNT.Examples.Minimal.not_structurallyPersistent⟩
