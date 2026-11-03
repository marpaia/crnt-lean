import CRNT.Examples.EnzymeQSSAUnconditional

/-! Axiom audit: Michaelis–Menten QSSA with moving substrate (field-map D19). -/

/-- info: 'ODE.coupled_dissipative_ceiling_forward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODE.coupled_dissipative_ceiling_forward

/-- info: 'ODE.coupled_dissipative_decay_forward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODE.coupled_dissipative_decay_forward

/-- info: 'CRNT.Enzyme.qssa_error_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Enzyme.qssa_error_le

/-- info: 'CRNT.Enzyme.qssa_error_decay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Enzyme.qssa_error_decay

/-- info: 'CRNT.Examples.Enzyme.qssa_error_le_enzyme' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Examples.Enzyme.qssa_error_le_enzyme

/-- info: 'CRNT.Examples.Enzyme.qssa_error_decay_enzyme' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CRNT.Examples.Enzyme.qssa_error_decay_enzyme
