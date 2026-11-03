import CRNT.Multistationarity.InheritanceDependent
import CRNT.Multistationarity.InheritanceAddSpecies
import CRNT.Examples.OneReactionAtom
import CRNT.Multistationarity.OneReactionUniqueness
import CRNT.Multistationarity.OneReactionExistence
import CRNT.Multistationarity.OneReactionReversible
import CRNT.Multistationarity.OneReactionReversibleUnique

/-! Axiom audit: Joshi–Shiu inheritance under dependent reactions (field-map M11). -/

/-- info: 'CRNT.Network.massActionJacobianCLM_mem_stoichSubspace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.massActionJacobianCLM_mem_stoichSubspace

/-- info: 'CRNT.Network.perturbedField_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.perturbedField_mem

/-- info: 'CRNT.Network.eventually_steadyState_branch_dependent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.eventually_steadyState_branch_dependent

/-- info: 'CRNT.Network.multistationarity_inherited_dependent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.multistationarity_inherited_dependent

/-- info: 'CRNT.Network.massActionVectorField_addSpecies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.massActionVectorField_addSpecies

/-- info: 'CRNT.Network.extNet_field_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.extNet_field_some

/-- info: 'CRNT.Network.restrict_extJacobian_slice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.restrict_extJacobian_slice

/-- info: 'CRNT.Network.eventually_steadyState_branch_addSpecies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.eventually_steadyState_branch_addSpecies

/-- info: 'CRNT.Network.addSpecies_stoichSubspace_eq_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.addSpecies_stoichSubspace_eq_top

/-- info: 'CRNT.Network.multistationarity_inherited_addSpecies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.multistationarity_inherited_addSpecies

/-- info: 'CRNT.Examples.OneReactionAtom.hasAlternatingArrowPattern_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Examples.OneReactionAtom.hasAlternatingArrowPattern_iff

/-- info: 'CRNT.Examples.OneReactionAtom.multistationary_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Examples.OneReactionAtom.multistationary_iff

/-- info: 'CRNT.Network.oneRxn_fullyOpen_field' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.oneRxn_fullyOpen_field

/-- info: 'CRNT.Network.oneRxn_no_two_levels' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.oneRxn_no_two_levels

/-- info: 'CRNT.Network.oneRxn_unique_steadyState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.oneRxn_unique_steadyState

/-- info: 'CRNT.Network.oneRxn_exists_two_steadyStates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.oneRxn_exists_two_steadyStates

/-- info: 'CRNT.Network.oneRxn_multistationary_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.oneRxn_multistationary_iff

/-- info: 'CRNT.Network.revPair_fullyOpen_field' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.revPair_fullyOpen_field

/-- info: 'CRNT.Network.revPair_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.revPair_core

/-- info: 'CRNT.Network.revPair_exists_two_steadyStates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.revPair_exists_two_steadyStates

/-- info: 'CRNT.no_two_zeros_of_deriv_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.no_two_zeros_of_deriv_neg

/-- info: 'CRNT.Network.weighted_sum_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.weighted_sum_lt_one

/-- info: 'CRNT.Network.revPair_slope_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.revPair_slope_neg

/-- info: 'CRNT.Network.logMono_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.logMono_hasDerivAt

/-- info: 'CRNT.Network.revPair_unique_steadyState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.revPair_unique_steadyState

/-- info: 'CRNT.Network.revPair_multistationary_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.revPair_multistationary_iff
