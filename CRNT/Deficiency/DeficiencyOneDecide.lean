import CRNT.Deficiency.DeficiencyOneHypotheses
import CRNT.Decision.DirectedReachability
import CRNT.Decision.Linkage
import Mathlib.Tactic.DeriveFintype
import CRNT.Basic.Complex
import CRNT.Basic.Reaction
import CRNT.Basic.Network

/-!
# Decidability of the terminal/linkage-structure condition

The third structural hypothesis of the deficiency-one theorem,
`OneTerminalSLCPerLinkageClass`, asks that each linkage class contain exactly one terminal
strong linkage class. This module makes that condition fully `Decidable` and `decide`-reducible
in the kernel.

The decision rests on a chain of computable instances over the finite vertex type of a
network's complexes:

* `instDecidableRelLinked`: linkage is a decidable relation, from `decidableLinked`;
* `instDecidableEqLinkageClass` / `instDecidableEqStrongLinkageClass`: the linkage and strong
  linkage quotients have decidable equality, via `Quotient.decidableEq`;
* `instDecidableIsTerminalSLClass`: terminality of a strong linkage class is decidable, lifting
  `Decidable (N.IsTerminalSLC a.val)` along the quotient;
* `instFintypeQuotientLinkageClass`: a *computable* `Fintype` on the linkage-class quotient, via
  `Quotient.fintype`, which is what lets `decide` reduce;
* `instDecidableOneTerminalSLCPerLinkageClass`: the condition itself, decidable by unfolding
  `ExistsUnique` and closing with the bounded-quantifier instances.

The bridge `isTerminalSLClass_iff_isTerminalSLC` lets a class-level terminality goal be rewritten
to the complex-level decidable predicate.

The per-linkage-class deficiency bound `δ_θ ≤ 1` is *not* decidable here:
`linkageStoichRank` is `Module.finrank` of a real submodule (noncomputable), and only a one-sided
computable lower bound exists for the whole-network rank. So `DeficiencyOneConditions` and the
full `DeficiencyOneHypotheses` remain undecidable; only the terminal/linkage-structure core is
delivered.

Every instance is supplied as an `inferInstanceAs`/term (never a tactic proof) so that no
`Eq.rec` is injected and the kernel can reduce `decide`.

Depends on: `CRNT.Deficiency.DeficiencyOneHypotheses`,
`CRNT.Decision.DirectedReachability`, `CRNT.Decision.Linkage`.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Linkage among the network's complexes is a decidable relation. -/
instance instDecidableRelLinked (N : Network S) : DecidableRel N.linkedSetoid.r :=
  fun a b => N.decidableLinked a b

/-- The linkage-class quotient has decidable equality. -/
instance instDecidableEqLinkageClass (N : Network S) :
    DecidableEq (Quotient N.linkedSetoid) :=
  Quotient.decidableEq

/-- The strong-linkage-class quotient has decidable equality. -/
instance instDecidableEqStrongLinkageClass (N : Network S) :
    DecidableEq (Quotient N.stronglyLinkedSetoid) :=
  Quotient.decidableEq

/-- Terminality of a strong linkage class is decidable. -/
instance instDecidableIsTerminalSLClass (N : Network S)
    (σ : Quotient N.stronglyLinkedSetoid) : Decidable (N.IsTerminalSLClass σ) :=
  inferInstanceAs
    (Decidable (Quotient.liftOn σ (fun c => N.IsTerminalSLC c.val)
      (fun _ _ hab => propext (N.isTerminalSLC_congr hab))))

/-- A *computable* `Fintype` on the linkage-class quotient, required for `decide` to reduce. -/
instance instFintypeQuotientLinkageClass (N : Network S) :
    Fintype (Quotient N.linkedSetoid) :=
  Quotient.fintype _

/-- **Condition (3) is decidable.** -/
instance instDecidableOneTerminalSLCPerLinkageClass (N : Network S) :
    Decidable N.OneTerminalSLCPerLinkageClass :=
  inferInstanceAs
    (Decidable (∀ θ : Quotient N.linkedSetoid,
      ∃ σ : Quotient N.stronglyLinkedSetoid,
        (N.strongToLinkage σ = θ ∧ N.IsTerminalSLClass σ) ∧
          ∀ y : Quotient N.stronglyLinkedSetoid,
            (N.strongToLinkage y = θ ∧ N.IsTerminalSLClass y) → y = σ))

/-- Class-level terminality unfolds to the complex-level decidable predicate. -/
theorem isTerminalSLClass_iff_isTerminalSLC (N : Network S)
    (c : {c : Complex S // c ∈ N.complexes}) :
    N.IsTerminalSLClass (Quotient.mk N.stronglyLinkedSetoid c) ↔ N.IsTerminalSLC c.val :=
  Iff.rfl

end Network

end CRNT

/-! ## Example: a reversible two-complex network -/

namespace CRNT.DeficiencyOneDecide.Example

open CRNT

inductive Species
  | A
  | B
  deriving DecidableEq, Repr

instance : Fintype Species where
  elems := {Species.A, Species.B}
  complete := by intro s; cases s <;> simp

open Species

def cA : Complex Species := fun s => match s with | A => 1 | B => 0
def cB : Complex Species := fun s => match s with | A => 0 | B => 1

inductive Rxn
  | r1
  | r2
  deriving DecidableEq, Repr

instance : Fintype Rxn where
  elems := {Rxn.r1, Rxn.r2}
  complete := by intro r; cases r <;> simp

def reaction : Rxn → Reaction Species
  | .r1 => { source := cA, target := cB }
  | .r2 => { source := cB, target := cA }

def N : Network Species :=
  { R := Rxn, decEqR := inferInstance, fintypeR := inferInstance, reaction := reaction }

/-- The reversible network `A ⇌ B` has one linkage class whose single strong linkage class is
terminal, so condition (3) holds and decides positively. -/
example : N.OneTerminalSLCPerLinkageClass := by decide

end CRNT.DeficiencyOneDecide.Example
