import CRNT.Stoich.Vector
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Finset.Powerset

/-!
# Siphons

A *siphon* is a set of species `P` such that every reaction producing a species of `P`
also consumes a species of `P`. In Petri-net terms this is the support of a structurally
trapped depletion: once every species of `P` is absent, no reaction can replenish it.
Siphons control which boundary faces of the positive orthant are forward-invariant for a
mass-action system, and *critical* siphons (those carrying no positive conservation-law
support) are the obstructions to persistence in the Angeli–De Leenheer–Sontag analysis.

Siphons are modelled as a `Finset` of species so that the siphon condition lands in a
`Decidable` class: reactant and product membership of a reaction is decidable directly
from its natural-number coefficients, the bounded existentials over `P` are decidable,
and the universal quantifier over the finite reaction index type is decidable. Concrete
networks therefore settle siphon questions by `decide`.

`IsCriticalSiphon` is a faithful `Prop` capturing the absence of a positive conservation
law supported exactly on `P`. Deciding criticality requires sign-restricted kernel
feasibility over the stoichiometric matrix and is not provided here; neither is the
persistence-soundness direction (no critical siphon ⇒ persistence), which needs an
ω-limit forward-invariance argument absent from this layer.

Depends on: `CRNT.Stoich.Vector`.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- A species `s` is a *reactant* of reaction `r` when its source coefficient is nonzero,
i.e. the reaction consumes `s`. -/
def IsReactant (N : Network S) (r : N.R) (s : S) : Prop :=
  (N.reaction r).source s ≠ 0

/-- A species `s` is a *product* of reaction `r` when its target coefficient is nonzero,
i.e. the reaction produces `s`. -/
def IsProduct (N : Network S) (r : N.R) (s : S) : Prop :=
  (N.reaction r).target s ≠ 0

instance (N : Network S) (r : N.R) (s : S) : Decidable (N.IsReactant r s) :=
  inferInstanceAs (Decidable ((N.reaction r).source s ≠ 0))

instance (N : Network S) (r : N.R) (s : S) : Decidable (N.IsProduct r s) :=
  inferInstanceAs (Decidable ((N.reaction r).target s ≠ 0))

/-- A `Finset` of species `P` is a *siphon* when every reaction that produces some species
of `P` also consumes some species of `P`. -/
def IsSiphon (N : Network S) (P : Finset S) : Prop :=
  ∀ r : N.R, (∃ s ∈ P, N.IsProduct r s) → (∃ s ∈ P, N.IsReactant r s)

instance decidableIsSiphon (N : Network S) (P : Finset S) : Decidable (N.IsSiphon P) :=
  inferInstanceAs (Decidable (∀ r : N.R, (∃ s ∈ P, N.IsProduct r s) → (∃ s ∈ P, N.IsReactant r s)))

/-- The empty set is a siphon: no reaction produces a species of `∅`, so the implication
holds vacuously. -/
theorem empty_isSiphon (N : Network S) : N.IsSiphon ∅ := by
  intro r h
  rcases h with ⟨s, hs, _⟩
  exact absurd hs (Finset.notMem_empty s)

/-- Siphons are closed under union: a reaction producing a species of `P ∪ Q` produces a
species of `P` or of `Q`, and the corresponding siphon supplies a consumed species. -/
theorem union_isSiphon (N : Network S) {P Q : Finset S}
    (hP : N.IsSiphon P) (hQ : N.IsSiphon Q) : N.IsSiphon (P ∪ Q) := by
  intro r h
  rcases h with ⟨s, hsPQ, hs⟩
  rw [Finset.mem_union] at hsPQ
  rcases hsPQ with hsP | hsQ
  · obtain ⟨t, htP, ht⟩ := hP r ⟨s, hsP, hs⟩
    exact ⟨t, Finset.mem_union_left Q htP, ht⟩
  · obtain ⟨t, htQ, ht⟩ := hQ r ⟨s, hsQ, hs⟩
    exact ⟨t, Finset.mem_union_right P htQ, ht⟩

/-- A *critical siphon* is a nonempty siphon `P` that carries no positive conservation law
supported exactly on `P`: there is no nonnegative vector `v`, strictly positive precisely
on `P`, that is orthogonal to every reaction vector. Critical siphons are the structural
obstructions to persistence. -/
def IsCriticalSiphon (N : Network S) (P : Finset S) : Prop :=
  P.Nonempty ∧ N.IsSiphon P ∧
    ¬ ∃ v : S → ℝ, (∀ s, 0 ≤ v s) ∧ (∀ s, 0 < v s ↔ s ∈ P) ∧
      (∀ r : N.R, ∑ s, v s * N.reactionVector r s = 0)

/-- A network *has no critical siphon* when none of its species subsets is a critical
siphon. This is the structural hypothesis underlying persistence. -/
def HasNoCriticalSiphon (N : Network S) : Prop :=
  ∀ P : Finset S, ¬ N.IsCriticalSiphon P

/-- A critical siphon is in particular a siphon. -/
theorem isCriticalSiphon_isSiphon (N : Network S) {P : Finset S}
    (h : N.IsCriticalSiphon P) : N.IsSiphon P :=
  h.2.1

/-- The empty set is not a critical siphon, since a critical siphon is nonempty. -/
theorem not_isCriticalSiphon_empty (N : Network S) : ¬ N.IsCriticalSiphon ∅ :=
  fun h => Finset.not_nonempty_empty h.1

/-- **No nonempty siphon ⇒ no critical siphon.** Every critical siphon is a nonempty siphon, so a
network with no nonempty siphon trivially has no critical siphon. This is the sound, Farkas-free
direction: deciding `IsCriticalSiphon` needs sign-restricted feasibility, but *excluding* it via the
absence of any nonempty siphon is purely structural and decidable — and (with weak reversibility and
complex balancing) yields persistence through `gac_of_hasNoCriticalSiphon`. -/
theorem hasNoCriticalSiphon_of_forall_not_isSiphon (N : Network S)
    (h : ∀ P : Finset S, P.Nonempty → ¬ N.IsSiphon P) : N.HasNoCriticalSiphon :=
  fun P hP => h P hP.1 hP.2.1

/-- A *minimal siphon* is a nonempty siphon none of whose proper nonempty subsets is a siphon. The
minimal siphons are the support-minimal structural traps; a candidate critical siphon is found among
them, so they are the species sets a persistence analysis (the consumer's feasibility check) tests. -/
def IsMinimalSiphon (N : Network S) (P : Finset S) : Prop :=
  P.Nonempty ∧ N.IsSiphon P ∧ ∀ Q ∈ P.powerset, Q.Nonempty → Q ≠ P → ¬ N.IsSiphon Q

instance decidableIsMinimalSiphon (N : Network S) (P : Finset S) :
    Decidable (N.IsMinimalSiphon P) := by unfold IsMinimalSiphon; infer_instance

/-- A minimal siphon is in particular a siphon. -/
theorem IsMinimalSiphon.isSiphon {N : Network S} {P : Finset S}
    (h : N.IsMinimalSiphon P) : N.IsSiphon P := h.2.1

/-- The finite set of minimal siphons of the network. -/
def minimalSiphons (N : Network S) : Finset (Finset S) :=
  (Finset.univ : Finset S).powerset.filter (fun P => N.IsMinimalSiphon P)

@[simp] theorem mem_minimalSiphons (N : Network S) (P : Finset S) :
    P ∈ N.minimalSiphons ↔ N.IsMinimalSiphon P := by
  unfold minimalSiphons
  rw [Finset.mem_filter, Finset.mem_powerset, and_iff_right (Finset.subset_univ P)]

end Network

end CRNT

namespace CRNT.Examples.SiphonReversiblePair

open CRNT

/-- Two species, `A` and `B`. -/
inductive Species
  | A
  | B
  deriving DecidableEq, Repr

instance : Fintype Species where
  elems := {Species.A, Species.B}
  complete := by intro s; cases s <;> simp

open Species

/-- The complex `A`. -/
def cA : Complex Species := fun s => match s with | A => 1 | B => 0

/-- The complex `B`. -/
def cB : Complex Species := fun s => match s with | A => 0 | B => 1

/-- Two reaction channels: forward `A → B` and backward `B → A`. -/
inductive Rxn
  | fwd
  | bwd
  deriving DecidableEq, Repr

instance : Fintype Rxn where
  elems := {Rxn.fwd, Rxn.bwd}
  complete := by intro r; cases r <;> simp

/-- The reaction map. -/
def rxn : Rxn → Reaction Species
  | .fwd => { source := cA, target := cB }
  | .bwd => { source := cB, target := cA }

/-- The reversible pair `A ⇌ B`. -/
def N : Network Species :=
  { R := Rxn, decEqR := inferInstance, fintypeR := inferInstance, reaction := rxn }

/-- The empty set is a siphon, decided end-to-end by `decidableIsSiphon`. -/
example : N.IsSiphon (∅ : Finset Species) := by decide

/-- The full species set is a siphon here: each reaction both produces and consumes a
species of `univ`. -/
example : N.IsSiphon (Finset.univ : Finset Species) := by decide

end CRNT.Examples.SiphonReversiblePair
