import Mathlib.Tactic.DeriveFintype
import CRNT.Basic.Complex
import CRNT.Basic.Reaction
import CRNT.Basic.Network
import CRNT.Stoich.Vector
import CRNT.Graph.Reachability
import CRNT.Graph.WeakReversibility

set_option backward.isDefEq.respectTransparency false

/-!
# Minimal example: a single irreversible reaction `A → B`

The smallest nontrivial network. It demonstrates building a `Network`, computing its
complex count, evaluating reaction vectors, and reasoning about (the failure of)
reachability. Being irreversible, it is **not** weakly reversible.
-/

namespace CRNT.Examples.Minimal

open CRNT

/-- Two species, `A` and `B`. -/
inductive Species
  | A
  | B
  deriving DecidableEq, Fintype, Repr

open Species

/-- The complex consisting of one molecule of `A`. -/
def cA : Complex Species := fun s => match s with | A => 1 | B => 0

/-- The complex consisting of one molecule of `B`. -/
def cB : Complex Species := fun s => match s with | A => 0 | B => 1

/-- A single reaction channel. -/
inductive Rxn
  | r1
  deriving DecidableEq, Fintype, Repr

/-- The reaction map: `r1 : A → B`. -/
def rxn : Rxn → Reaction Species
  | .r1 => { source := cA, target := cB }

/-- The network `A → B`. -/
def N : Network Species :=
  { R := Rxn, decEqR := inferInstance, fintypeR := inferInstance, reaction := rxn }

theorem cA_ne_cB : cA ≠ cB := by decide

/-- The network has exactly two complexes. -/
theorem numComplexes_eq : N.numComplexes = 2 := by decide

/-- There is one reaction. -/
theorem numReactions_eq : N.numReactions = 1 := by decide

/-- The reaction vector of `r1` is `B - A`: `-1` on `A` and `+1` on `B`. -/
theorem reactionVector_r1 :
    N.reactionVector .r1 = fun s => match s with | A => (-1 : ℝ) | B => 1 := by
  funext s
  cases s <;>
    simp [Network.reactionVector, N, rxn, Reaction.vector, cA, cB]

/-- From `B` no reaction fires, so `B` reaches nothing new. -/
theorem not_directlyReacts_from_cB (d : Complex Species) :
    ¬ N.DirectlyReacts cB d := by
  rintro ⟨r, hs, -⟩
  cases r
  exact cA_ne_cB hs

/-- The network is not weakly reversible: there is no directed path from `B` back to
`A`. -/
theorem not_weaklyReversible : ¬ N.WeaklyReversible := by
  intro h
  have hr : Relation.ReflTransGen N.DirectlyReacts cB cA := h .r1
  rcases Relation.ReflTransGen.cases_head hr with heq | ⟨e, hedge, -⟩
  · exact cA_ne_cB heq.symm
  · exact not_directlyReacts_from_cB e hedge

end CRNT.Examples.Minimal
