import Mathlib.Tactic.DeriveFintype
import CRNT.Basic.Complex
import CRNT.Basic.Reaction
import CRNT.Basic.Network
import CRNT.Graph.Reachability
import CRNT.Graph.WeakReversibility
import CRNT.Interop.Certificates

set_option backward.isDefEq.respectTransparency false

/-!
# Generated-certificate example

This module mirrors the shape of a Lean file that an external tool (a CRN compiler,
SBML/SBOL exporter, or AI design system) would emit: it declares a species type, the
complexes, an indexed reaction type, the network, and then *checks* structural
properties. Reachability claims are discharged with the verified walk checker
`reaches_of_walk`, whose `Bool` side closes by `decide` on the concrete network.

See `docs/generated-certificates.md` for the emission contract.
-/

namespace CRNT.Generated.Example

open CRNT

inductive Species
  | A
  | B
  deriving DecidableEq, Fintype, Repr

open Species

def cA : Complex Species := fun s => match s with | A => 1 | B => 0
def cB : Complex Species := fun s => match s with | A => 0 | B => 1

inductive Rxn
  | r1
  | r2
  deriving DecidableEq, Fintype, Repr

def reaction : Rxn → Reaction Species
  | .r1 => { source := cA, target := cB }
  | .r2 => { source := cB, target := cA }

def N : Network Species :=
  { R := Rxn, decEqR := inferInstance, fintypeR := inferInstance, reaction := reaction }

/-- Certificate: `B` reaches `A` via the explicit one-step walk `[A]`. The endpoint
condition and the walk check are both closed by `decide`. -/
example : N.Reaches cB cA :=
  N.reaches_of_walk cB cA [cA] (by decide) (by decide)

/-- Certificate: the network is weakly reversible, with a checked return walk for each
reaction. -/
example : N.WeaklyReversible := by
  intro r
  cases r
  · exact N.reaches_of_walk cB cA [cA] (by decide) (by decide)
  · exact N.reaches_of_walk cA cB [cB] (by decide) (by decide)

/-- Certificate: the network has exactly two complexes. -/
example : N.numComplexes = 2 := by decide

end CRNT.Generated.Example
