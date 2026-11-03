import CRNT.Multistationarity.TrueChemistrySRCriterion

/-!
# Axiom audit for the Banaji--Craciun route to the true-SR theorem

Imports only the true-SR criterion module (and through it the five `BC*` modules), so it builds in
about a minute.  Every entry must be `[propext, Classical.choice, Quot.sound]`.
-/

/-- info: 'CRNT.Network.stronglyConcordant_fullyOpen_of_trueSRCriterion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.stronglyConcordant_fullyOpen_of_trueSRCriterion

/-- info: 'CRNT.Network.stronglyConcordant_fullyOpen_of_trueSRCriterion_bc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.stronglyConcordant_fullyOpen_of_trueSRCriterion_bc

/-- info: 'CRNT.Network.stronglyConcordant_of_trueSRCriterion_of_weaklyReversible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.stronglyConcordant_of_trueSRCriterion_of_weaklyReversible

/-- info: 'CRNT.Network.injective_of_trueSRCriterion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.injective_of_trueSRCriterion

/-- info: 'CRNT.Network.bc_coeff_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.bc_coeff_nonneg

/-- info: 'CRNT.Network.det_bcProduct_eq_zero_of_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.det_bcProduct_eq_zero_of_witness

/-- info: 'CRNT.Network.CyclePair.sToRIntersection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.CyclePair.sToRIntersection

/-- info: 'CRNT.Network.CycleChannels.signed_weight_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.CycleChannels.signed_weight_eq

/-- info: 'CRNT.DetCycle.det_nonneg_of_negCycles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.DetCycle.det_nonneg_of_negCycles

/-- info: 'CRNT.DetCycle.det_mul_eq_sum_columns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.DetCycle.det_mul_eq_sum_columns
