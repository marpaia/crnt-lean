import CRNT.Design.ACR
import CRNT.Decision.DirectedReachability
import CRNT.Decision.Linkage

/-!
# Decidable structural check for the Shinar–Feinberg ACR hypotheses

The Shinar–Feinberg sufficient condition for absolute concentration robustness asks for two
non-terminal complexes lying in distinct linkage classes and differing in exactly one species,
inside a deficiency-one network. The discrete graph-structural part of that condition is a
finite decision problem: non-terminality of a strong linkage class is decidable, linkage is
decidable, and the single-species-difference comparison is decidable. This module packages
exactly that decidable fragment.

`HasShinarFeinbergPair` is the existential structural predicate over complex indices; it is
phrased with `¬ N.Linked` rather than `N.classOf _ ≠ N.classOf _` so that the synthesized
`Decidable` instance reduces under `decide` without an `Eq.rec` obstruction. The bridge
`classOf_ne_iff_not_linked` recovers the linkage-class formulation. Soundness runs both ways:
the structural hypotheses yield such a pair (`HasShinarFeinbergPair.of_hypotheses`), and a pair
together with the deficiency-one hypotheses reconstitutes the full
`ShinarFeinbergHypotheses` (`ShinarFeinbergHypotheses.ofPair`). The deficiency-one condition
itself is not a finite decision and is supplied externally.

Depends on: `CRNT.Design.ACR`,
`CRNT.Decision.DirectedReachability`, `CRNT.Decision.Linkage`.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Decidable structural witness for Shinar–Feinberg ACR in `s`.** There exist two complex
indices `a` and `b`, both non-terminal, not linked to each other, agreeing away from `s`, and
differing at `s`. The non-linkage is stated as `¬ N.Linked a.val b.val` (rather than distinct
linkage classes) so the predicate is decidable and reduces under `decide`. -/
def HasShinarFeinbergPair (N : Network S) (s : S) : Prop :=
  ∃ a b : N.ComplexIdx, ¬ N.IsTerminalSLC a.val ∧ ¬ N.IsTerminalSLC b.val ∧
    ¬ N.Linked a.val b.val ∧ (∀ t, t ≠ s → a.val t = b.val t) ∧ a.val s ≠ b.val s

instance instDecidableHasShinarFeinbergPair (N : Network S) (s : S) :
    Decidable (N.HasShinarFeinbergPair s) :=
  inferInstanceAs (Decidable (∃ _ _, _))

/-- **The species carrying a structural Shinar–Feinberg ACR witness.** The finite set of species
`s` for which `HasShinarFeinbergPair s` holds, computed by filtering the species. This is the
decidable structural fragment of ACR; the deficiency-one side condition is supplied externally. -/
def acrSpecies (N : Network S) : Finset S :=
  Finset.univ.filter (fun s => N.HasShinarFeinbergPair s)

@[simp] theorem mem_acrSpecies (N : Network S) (s : S) :
    s ∈ N.acrSpecies ↔ N.HasShinarFeinbergPair s := by
  simp [acrSpecies]

/-- **Distinct linkage classes versus non-linkage.** Two complex indices have different linkage
classes exactly when they are not linked. This is the human-facing bridge between the
`classOf`-based formulation in `ShinarFeinbergHypotheses` and the `¬ N.Linked` formulation used
in the decidable predicate. -/
theorem classOf_ne_iff_not_linked (N : Network S) (a b : N.ComplexIdx) :
    N.classOf a ≠ N.classOf b ↔ ¬ N.Linked a.val b.val := by
  unfold classOf
  rw [ne_eq, Quotient.eq]
  rfl

/-- **The structural hypotheses yield a structural pair.** Discarding the deficiency-one field,
the two complexes of a `ShinarFeinbergHypotheses` witness `HasShinarFeinbergPair`. -/
theorem HasShinarFeinbergPair.of_hypotheses {N : Network S} {s : S}
    (H : N.ShinarFeinbergHypotheses s) : N.HasShinarFeinbergPair s := by
  refine ⟨⟨H.c, H.hc⟩, ⟨H.d, H.hd⟩, H.nonTerminalC, H.nonTerminalD, ?_, H.differOnlyAt, H.differAt⟩
  exact (classOf_ne_iff_not_linked N ⟨H.c, H.hc⟩ ⟨H.d, H.hd⟩).mp H.diffClass

/-- **A structural pair plus deficiency-one rebuilds the full hypotheses.** The decidable check
covers every Shinar–Feinberg condition except the deficiency-one constraint, which is supplied
here as an explicit input. -/
noncomputable def ShinarFeinbergHypotheses.ofPair {N : Network S} {s : S}
    (hpair : N.HasShinarFeinbergPair s) (hdef : N.DeficiencyOneHypotheses) :
    N.ShinarFeinbergHypotheses s :=
  let a := hpair.choose
  let b := hpair.choose_spec.choose
  let ⟨hntC, hntD, hnotLinked, hdiffOnly, hdiffAt⟩ := hpair.choose_spec.choose_spec
  { c := a.val
    d := b.val
    hc := a.2
    hd := b.2
    nonTerminalC := hntC
    nonTerminalD := hntD
    diffClass := (classOf_ne_iff_not_linked N a b).mpr hnotLinked
    differOnlyAt := hdiffOnly
    differAt := hdiffAt
    defOne := hdef }

end Network

/-! ## A concrete decidable structural witness -/

namespace Examples.ACRPair

open CRNT

/-- Three species. -/
inductive Species
  | A
  | P
  | Q
  deriving DecidableEq, Repr

instance : Fintype Species where
  elems := {Species.A, Species.P, Species.Q}
  complete := by intro s; cases s <;> simp

open Species

/-- The complex `A`. -/
def cA : Complex Species := fun s => match s with | A => 1 | _ => 0

/-- The complex `2A`. -/
def c2A : Complex Species := fun s => match s with | A => 2 | _ => 0

/-- The complex `P`. -/
def cP : Complex Species := fun s => match s with | P => 1 | _ => 0

/-- The complex `Q`. -/
def cQ : Complex Species := fun s => match s with | Q => 1 | _ => 0

/-- Two reactions: `A → P` and `2A → Q`. -/
inductive Rxn
  | r1
  | r2
  deriving DecidableEq, Repr

instance : Fintype Rxn where
  elems := {Rxn.r1, Rxn.r2}
  complete := by intro r; cases r <;> simp

/-- The reaction map. -/
def rxn : Rxn → Reaction Species
  | .r1 => { source := cA, target := cP }
  | .r2 => { source := c2A, target := cQ }

/-- The toy network with non-terminal complexes `A` and `2A` in distinct linkage classes
differing only in species `A`. -/
def N : Network Species :=
  { R := Rxn, decEqR := inferInstance, fintypeR := inferInstance, reaction := rxn }

/-- The structural Shinar–Feinberg pair condition holds in species `A`, decided by computation. -/
example : N.HasShinarFeinbergPair Species.A := by decide

end Examples.ACRPair

end CRNT
