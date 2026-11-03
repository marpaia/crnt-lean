import CRNTFrontier

/-!
# Axiom audit for the conditional oscillation bundles

The bundle constructors below take explicit mathematical targets as hypotheses. These guards
check their axiom dependencies without treating those hypotheses as proved theorems. The
theorem endpoints are audited separately in `test.FrontierAuditCurrent`.
-/

/-! ## The closure claim -/

/-- info: 'CRNT.completeOscillationKernelBundle_of_targets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.completeOscillationKernelBundle_of_targets

/-! ## Its five fields, pinned individually so a failure localizes -/

/-- info: 'CRNT.planarKernelBundle_of_targets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.planarKernelBundle_of_targets

/-- info: 'CRNT.vassenaKernelBundle_of_targets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.vassenaKernelBundle_of_targets

/-- info: 'CRNT.parameterRichCoreKernelBundle_of_targets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.parameterRichCoreKernelBundle_of_targets

/-- info: 'CRNT.stabilityInheritanceKernelBundle_of_targets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.stabilityInheritanceKernelBundle_of_targets

/-- info: 'CRNT.recipeZeroKernelBundle_of_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.recipeZeroKernelBundle_of_target

/-! ## The three results the handoff singles out as the deliverables -/

/-- info: 'CRNT.Network.floquetOrbitalStability_of_tube' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.floquetOrbitalStability_of_tube

/-- info: 'CRNT.Network.nondegenerateDependentReactionPersistence_of_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.nondegenerateDependentReactionPersistence_of_target

/-- info: 'CRNT.Network.stableDependentReactionPersistence_of_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Network.stableDependentReactionPersistence_of_target

/-!
The Lotka negative controls are compiled in `test.LotkaNonVacuity`; they check the structural
exclusion verdict on a network outside both exclusion routes. They do not establish the general
Floquet or inheritance targets supplied to the constructors above.
-/
