import Mathlib.Tactic.DeriveFintype
import CRNT.Basic.Complex
import CRNT.Basic.Reaction
import CRNT.Basic.Network
import CRNT.Graph.Reachability
import CRNT.Graph.WeakReversibility

set_option backward.isDefEq.respectTransparency false

/-!
# Irreversible chain `A → B → C`

A linear, irreversible pathway. It has three species, three complexes, two reactions,
and one linkage class, but is **not** weakly reversible: nothing returns to `A` or `B`
once `C` is reached. This module proves the complex count and the failure of weak
reversibility.
-/

namespace CRNT.Examples.IrreversibleChain

open CRNT

/-- Three species. -/
inductive Species
  | A
  | B
  | C
  deriving DecidableEq, Fintype, Repr

open Species

/-- The complex `A`. -/
def cA : Complex Species := fun s => match s with | A => 1 | _ => 0

/-- The complex `B`. -/
def cB : Complex Species := fun s => match s with | B => 1 | _ => 0

/-- The complex `C`. -/
def cC : Complex Species := fun s => match s with | C => 1 | _ => 0

/-- Two reactions: `A → B` and `B → C`. -/
inductive Rxn
  | r1
  | r2
  deriving DecidableEq, Fintype, Repr

/-- The reaction map. -/
def rxn : Rxn → Reaction Species
  | .r1 => { source := cA, target := cB }
  | .r2 => { source := cB, target := cC }

/-- The network `A → B → C`. -/
def N : Network Species :=
  { R := Rxn, decEqR := inferInstance, fintypeR := inferInstance, reaction := rxn }

/-- `n = 3`: the network has three complexes. -/
theorem numComplexes_eq : N.numComplexes = 3 := by decide

/-- There are two reactions. -/
theorem numReactions_eq : N.numReactions = 2 := by decide

/-- No reaction has source `C`, so `C` reaches nothing new. -/
theorem not_directlyReacts_from_cC (d : Complex Species) :
    ¬ N.DirectlyReacts cC d := by
  rintro ⟨r, hs, -⟩
  cases r <;> exact absurd hs (by decide)

/-- The network is not weakly reversible: the reaction `B → C` has no return path from
`C` to `B`. -/
theorem not_weaklyReversible : ¬ N.WeaklyReversible := by
  intro h
  have hr : Relation.ReflTransGen N.DirectlyReacts cC cB := h .r2
  rcases Relation.ReflTransGen.cases_head hr with heq | ⟨e, hedge, -⟩
  · exact absurd heq (by decide)
  · exact not_directlyReacts_from_cC e hedge

end CRNT.Examples.IrreversibleChain
