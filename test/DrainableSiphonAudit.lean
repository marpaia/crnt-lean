import CRNT.Persistence.OrbitClosureSiphon
import CRNT.Examples.InflowNoDrainable
import CRNT.Examples.MinimalDGCritical

/-! Axiom audit: Deshpande–Gopalkrishnan Theorem 6.2 without boundedness (field-map D11). -/

/-- info: 'CRNT.Persistence.interval_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Persistence.interval_bounds

/-- info: 'CRNT.Persistence.exit_time_contradiction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Persistence.exit_time_contradiction

/-- info: 'CRNT.Network.orbitClosure_nonnegative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.orbitClosure_nonnegative

/-- info: 'CRNT.Network.isSiphon_zeroSet_of_orbitClosure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.isSiphon_zeroSet_of_orbitClosure

/-- info: 'CRNT.Network.isDrainableSiphon_zeroSet_of_orbitClosure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.isDrainableSiphon_zeroSet_of_orbitClosure

/-- info: 'CRNT.Network.orbitClosure_positive_of_hasNoDrainableSiphon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.orbitClosure_positive_of_hasNoDrainableSiphon

/-- info: 'CRNT.Network.omegaLimit_positive_of_hasNoDrainableSiphon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.omegaLimit_positive_of_hasNoDrainableSiphon

/-- info: 'CRNT.Network.orbitClosure_positive_of_weaklyReversible_hasNoSelfReplicableSiphon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.orbitClosure_positive_of_weaklyReversible_hasNoSelfReplicableSiphon

/-- info: 'CRNT.Examples.InflowNoDrainable.hasNoDrainableSiphon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Examples.InflowNoDrainable.hasNoDrainableSiphon

/-- info: 'CRNT.gordan_alternative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.gordan_alternative

/-- info: 'CRNT.Network.isSiphon_support_of_nonincreasing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.isSiphon_support_of_nonincreasing

/-- info: 'CRNT.Network.fluxDrainable_or_fluxSelfReplicable_of_minimalDGCritical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.fluxDrainable_or_fluxSelfReplicable_of_minimalDGCritical

/-- info: 'CRNT.Network.drainable_or_selfReplicable_of_minimalDGCritical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.drainable_or_selfReplicable_of_minimalDGCritical

/-- info: 'CRNT.Network.isDGCritical_of_isFluxDrainable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.isDGCritical_of_isFluxDrainable

/-- info: 'CRNT.Network.isDGCritical_of_isFluxSelfReplicable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.isDGCritical_of_isFluxSelfReplicable

/-- info: 'CRNT.Network.isCriticalSiphon_of_isDGCriticalSiphon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.isCriticalSiphon_of_isDGCriticalSiphon

/-- info: 'CRNT.Examples.CriticalDichotomyCE.not_minimalCriticalSiphonFluxDichotomy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Examples.CriticalDichotomyCE.not_minimalCriticalSiphonFluxDichotomy

/-- info: 'CRNT.Examples.CriticalDichotomyCE.not_isDGCritical_univ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Examples.CriticalDichotomyCE.not_isDGCritical_univ

/-- info: 'CRNT.Examples.Minimal.isMinimalDGCriticalSiphon_A' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Examples.Minimal.isMinimalDGCriticalSiphon_A

-- non-vacuity: the hypothesis holds for `0 ⇌ A`
example : CRNT.Examples.InflowNoDrainable.N.HasNoDrainableSiphon :=
  CRNT.Examples.InflowNoDrainable.hasNoDrainableSiphon

-- non-vacuity of the corrected dichotomy hypothesis
example : CRNT.Examples.Minimal.N.IsMinimalDGCriticalSiphon {CRNT.Examples.Minimal.Species.A} :=
  CRNT.Examples.Minimal.isMinimalDGCriticalSiphon_A

-- the repository's exact-support dichotomy is false
example : ¬ CRNT.Examples.CriticalDichotomyCE.N.MinimalCriticalSiphonFluxDichotomy :=
  CRNT.Examples.CriticalDichotomyCE.not_minimalCriticalSiphonFluxDichotomy
