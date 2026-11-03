import Mathlib.Tactic.DeriveFintype
import CRNT.Basic.Complex
import CRNT.Basic.Reaction
import CRNT.Basic.Network
import CRNT.Stoich.Vector
import CRNT.Kinetics.Concentration
import CRNT.Kinetics.MassAction

set_option backward.isDefEq.respectTransparency false

/-!
# Enzyme mechanism `E + S ⇌ ES → E + P`

The Michaelis–Menten mechanism: an enzyme `E` binds substrate `S` to form a complex
`ES`, which either dissociates back or turns over to release product `P` and free
enzyme. This module demonstrates complexes with multiple species and proves the total-
enzyme conservation law `d([E] + [ES])/dt = 0`, a structural fact independent of the
rate constants.
-/

namespace CRNT.Examples.Enzyme

open CRNT

/-- Four species: free enzyme `E`, substrate `S`, the enzyme–substrate complex `ES`,
and product `P`. -/
inductive Species
  | E
  | S
  | ES
  | P
  deriving DecidableEq, Fintype, Repr

open Species

/-- The complex `E + S`. -/
def cES_sub : Complex Species := fun s => match s with | E => 1 | S => 1 | _ => 0
/-- The bound complex `ES`. -/
def cESbound : Complex Species := fun s => match s with | ES => 1 | _ => 0
/-- The complex `E + P`. -/
def cEP : Complex Species := fun s => match s with | E => 1 | P => 1 | _ => 0

/-- Three reactions: binding, unbinding, and catalysis. -/
inductive Rxn
  | bind
  | unbind
  | catalyze
  deriving DecidableEq, Fintype, Repr

/-- The reaction map. -/
def rxn : Rxn → Reaction Species
  | .bind     => { source := cES_sub,  target := cESbound }
  | .unbind   => { source := cESbound, target := cES_sub }
  | .catalyze => { source := cESbound, target := cEP }

/-- The enzyme network. -/
def N : Network Species :=
  { R := Rxn, decEqR := inferInstance, fintypeR := inferInstance, reaction := rxn }

/-- `n = 3`: the three complexes are `E + S`, `ES`, and `E + P`. -/
theorem numComplexes_eq : N.numComplexes = 3 := by decide

/-- There are three reactions. -/
theorem numReactions_eq : N.numReactions = 3 := by decide

/-- Each reaction conserves total enzyme: the sum of the `E` and `ES` entries of every
reaction vector is zero. -/
theorem reactionVector_enzyme_balanced (r : N.R) :
    N.reactionVector r E + N.reactionVector r ES = 0 := by
  cases r <;>
    simp [Network.reactionVector, N, rxn, Reaction.vector, cES_sub, cESbound, cEP]

/-- **Total enzyme is conserved.** For every choice of rate constants and every
concentration, `d([E] + [ES])/dt = 0`. -/
theorem total_enzyme_conserved (κ : Network.RateConstants N) (x : Concentration Species) :
    N.massActionVectorField κ x E + N.massActionVectorField κ x ES = 0 := by
  rw [Network.massActionVectorField_apply, Network.massActionVectorField_apply,
    ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro r _
  rw [← mul_add, reactionVector_enzyme_balanced r, mul_zero]

end CRNT.Examples.Enzyme
