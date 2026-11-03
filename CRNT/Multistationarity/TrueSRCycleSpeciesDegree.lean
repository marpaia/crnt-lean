import CRNT.Multistationarity.TrueChemistrySRCriterion

/-!
# The aggregate causal degree of a cycle species is exactly two

At every species vertex of the cycle `C`, the **aggregate class flux** is completely determined.
Under `hSR`, a cycle reaction whose class is not one of the two neighbours of that species has
*zero* flux there (`nonAdjacent_cycleClassFlux_eq_zero`), while the two neighbours have strictly
opposite signs, pinned by the s-cycle's causal orientation `hcausal`/`hopp`.  Concretely, at the
vertex `C.species b`:

* `C.reaction b` has a **strictly negative** product — it is the reaction whose *left* edge meets
  `C.species b`;
* `C.reaction ((finRotate n).symm b)` has a **strictly positive** product — it is the reaction whose
  *right* edge meets `C.species b`;
* every other cycle reaction has product exactly `0`.

So the aggregate causal degree of a cycle species **restricted to cycle classes** is exactly one out
and one in — degree two, with no slack.  This is the formal content of DEAD-ENDS B-5 ("`hopp` /
`hcausal` / `¬hnc` are already sharp"), and it has one sharp consequence for the Hole B residue.

## Why this matters at the residue

At `TrueChemistrySRCriterion.lean:8579` the minimal aggregate causal path `Q0` starts at an
**on-cycle species** `s0` and every later vertex is off the cycle (`hQ0late`).  A causal edge out of
a species vertex requires a strictly negative class flux there, and by the trichotomy below a
*cycle* class can only provide that if it is `C.reaction b` — which **is** a cycle vertex, forbidden
by `hQ0late`.  Hence:

* `negCausalStep_from_cycleSpecies`: **the first hop out of a cycle species lands on
  `C.reaction b`, or on an off-cycle class that drains the cycle species.**  That dichotomy is the
  whole of the residue, and the second alternative is the ear's off-cycle end.

* `no_escape_from_cycleSpecies`: conversely, if no off-cycle class drains any cycle species, the
  residue branch is closed outright (`False`).  The Hole B residue is therefore **equivalent to the
  single named proposition `no_offCycle_negFlux`**.

* `exists_offCycle_negFlux_class`: the positive form — under `¬ no_offCycle_negFlux` the escape
  necessarily produces an off-cycle class `ρ` with a strictly negative class flux at a cycle
  species.  That is the datum DEAD-ENDS B-3 records as missing, in the correctly scoped form
  (`hrest` itself cannot be discharged, B-3).

## Note on `import`

This module **does** import `TrueChemistrySRCriterion` (it needs `trueInternalClassFlux`,
`nonAdjacent_cycleClassFlux_eq_zero`, `TrueInternalAggregateCausalEdge`, `ActiveAggregateTrueReaction`
and `CRNT.RelPath`).  None of the declarations below depends on the `sorry` in that file and none of
the declarations *defined after* it is used; `#print axioms` on each reports only
`[propext, Classical.choice, Quot.sound]`.  (Contrast the A.6 Case-2 port, which must not import it
at all — DEAD-ENDS B-12.)
-/

namespace CRNT.Network

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S} {n : ℕ}
  {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}

namespace TrueSRCycle

variable (C : N.TrueSRCycle n)

/-- The successor index used by `C.right_species`: `finRotate n i` is `⟨(i.1 + 1) % n, _⟩`. -/
theorem finRotate_val (C : N.TrueSRCycle n) (i : Fin n) :
    (finRotate n i).1 = (i.1 + 1) % n := by
  have hn := C.nontrivial
  have hn1 : 1 < n := by omega
  have h := congrArg Fin.val (finRotate_apply i)
  simpa [Fin.add_def, hn1] using h

/-- **The cycle's own left-edge reaction is negative at that species.**  Restating `hopp` at the
index itself rather than at its successor. -/
theorem hoppAt (C : N.TrueSRCycle n)
    (hopp : ∀ i : Fin n,
      N.trueInternalClassFlux α (C.reaction (finRotate n i)) (C.species (finRotate n i)) *
        σ (C.species (finRotate n i)) < 0) (j : Fin n) :
    N.trueInternalClassFlux α (C.reaction j) (C.species j) * σ (C.species j) < 0 := by
  have hh := hopp ((finRotate n).symm j)
  rwa [Equiv.apply_symm_apply] at hh

/-- **The cycle's own right-edge reaction is positive at that species.**  Restating `hcausal` at
the index itself: `(finRotate n).symm j` is the reaction whose *right* edge meets `C.species j`. -/
theorem hcausalAt (C : N.TrueSRCycle n)
    (hcausal : ∀ i : Fin n,
      0 < N.trueInternalClassFlux α (C.reaction i) (C.species (finRotate n i)) *
        σ (C.species (finRotate n i))) (j : Fin n) :
    0 < N.trueInternalClassFlux α (C.reaction ((finRotate n).symm j)) (C.species j) *
      σ (C.species j) := by
  have hh := hcausal ((finRotate n).symm j)
  rwa [Equiv.apply_symm_apply] at hh

/-- **Non-neighbouring cycle classes have zero flux at a cycle species.**  `nonAdjacent_cycle-
ClassFlux_eq_zero` in the `(a, b)` order used by the trichotomy below. -/
theorem classFlux_eq_zero_of_nonNeighbour (C : N.TrueSRCycle n)
    (hsep : N.ReactantProductSeparated) (hSR : N.TrueSRStrongCriterion) (hCeven : C.Even)
    (a b : Fin n) (hab : a ≠ b) (hba : b.1 ≠ (a.1 + 1) % n) :
    N.trueInternalClassFlux α (C.reaction a) (C.species b) = 0 :=
  N.nonAdjacent_cycleClassFlux_eq_zero hsep hSR C hCeven b a
    (fun h => hab (Fin.ext h)) (fun hh => hba hh.symm)

/-- **The degree-two content of a cycle species, first half: a strictly negative aggregate flux
at `C.species b` comes from the cycle reaction `C.reaction b` and from nothing else.**

So a cycle species has out-degree exactly `1` over the cycle classes, and the unique out-neighbour
is the reaction carrying its *left* edge. -/
theorem negFlux_eq_leftEdge (C : N.TrueSRCycle n) (hsep : N.ReactantProductSeparated)
    (hSR : N.TrueSRStrongCriterion) (hCeven : C.Even)
    (hcausal : ∀ i : Fin n,
      0 < N.trueInternalClassFlux α (C.reaction i) (C.species (finRotate n i)) *
        σ (C.species (finRotate n i)))
    (a b : Fin n)
    (h : N.trueInternalClassFlux α (C.reaction a) (C.species b) * σ (C.species b) < 0) :
    a = b := by
  have hne0 : N.trueInternalClassFlux α (C.reaction a) (C.species b) ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at h
    exact (lt_irrefl 0) h
  have hsucc : Fin n := ⟨(a.1 + 1) % n, Nat.mod_lt _ (by have := C.nontrivial; omega)⟩
  by_cases h1 : a = b
  · exact h1
  by_cases h2 : b.1 = (a.1 + 1) % n
  · exfalso
    have hfin : b = finRotate n a := Fin.ext (h2.trans (C.finRotate_val a).symm)
    rw [hfin] at h
    have hh := hcausal a
    linarith
  · exact absurd hne0 (fun hz => hz (classFlux_eq_zero_of_nonNeighbour C hsep hSR hCeven a b h1 h2))

/-- **The degree-two content of a cycle species, second half: a strictly positive aggregate flux
at `C.species b` comes from the reaction carrying its *right* edge and from nothing else.** -/
theorem posFlux_eq_rightEdge (C : N.TrueSRCycle n) (hsep : N.ReactantProductSeparated)
    (hSR : N.TrueSRStrongCriterion) (hCeven : C.Even)
    (hcausal : ∀ i : Fin n,
      0 < N.trueInternalClassFlux α (C.reaction i) (C.species (finRotate n i)) *
        σ (C.species (finRotate n i)))
    (hopp : ∀ i : Fin n,
      N.trueInternalClassFlux α (C.reaction (finRotate n i)) (C.species (finRotate n i)) *
        σ (C.species (finRotate n i)) < 0)
    (a b : Fin n)
    (h : 0 < N.trueInternalClassFlux α (C.reaction a) (C.species b) * σ (C.species b)) :
    b.1 = (a.1 + 1) % n := by
  have hne0 : N.trueInternalClassFlux α (C.reaction a) (C.species b) ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at h
    exact (lt_irrefl 0) h
  by_cases h1 : a = b
  · exfalso
    have hh := hoppAt C hopp a
    rw [h1] at h
    rw [h1] at hh
    linarith
  by_cases h2 : b.1 = (a.1 + 1) % n
  · exact h2
  · exact absurd hne0 (fun hz => hz (classFlux_eq_zero_of_nonNeighbour C hsep hSR hCeven a b h1 h2))

/-- **The trichotomy — the degree-two content in one statement.**  The aggregate class flux of a
cycle reaction at a cycle species is nonzero only at that reaction's two cycle neighbours; there
it has the sign dictated by the orientation.  Equivalently: the aggregate causal degree of a cycle
species over the cycle classes is exactly one out and one in. -/
theorem classFlux_trichotomy (C : N.TrueSRCycle n) (hsep : N.ReactantProductSeparated)
    (hSR : N.TrueSRStrongCriterion) (hCeven : C.Even)
    (hcausal : ∀ i : Fin n,
      0 < N.trueInternalClassFlux α (C.reaction i) (C.species (finRotate n i)) *
        σ (C.species (finRotate n i)))
    (hopp : ∀ i : Fin n,
      N.trueInternalClassFlux α (C.reaction (finRotate n i)) (C.species (finRotate n i)) *
        σ (C.species (finRotate n i)) < 0)
    (a b : Fin n) :
    (0 < N.trueInternalClassFlux α (C.reaction a) (C.species b) * σ (C.species b) ∧
        b.1 = (a.1 + 1) % n) ∨
      (N.trueInternalClassFlux α (C.reaction a) (C.species b) * σ (C.species b) = 0 ∧
        a ≠ b ∧ b.1 ≠ (a.1 + 1) % n) ∨
      (N.trueInternalClassFlux α (C.reaction a) (C.species b) * σ (C.species b) < 0 ∧ a = b) := by
  have hsign : 0 < N.trueInternalClassFlux α (C.reaction a) (C.species b) * σ (C.species b) ∨
      (0 = N.trueInternalClassFlux α (C.reaction a) (C.species b) * σ (C.species b)) ∨
      N.trueInternalClassFlux α (C.reaction a) (C.species b) * σ (C.species b) < 0 :=
    lt_trichotomy (0 : ℝ)
      (N.trueInternalClassFlux α (C.reaction a) (C.species b) * σ (C.species b))
  rcases hsign with hlt | heq | hgt
  · exact Or.inl ⟨hlt, posFlux_eq_rightEdge C hsep hSR hCeven hcausal hopp a b hlt⟩
  · by_cases h1 : a = b
    · exfalso
      have hh := hoppAt C hopp a
      rw [h1] at heq
      rw [h1] at hh
      linarith
    by_cases h2 : b.1 = (a.1 + 1) % n
    · exfalso
      have hfin : b = finRotate n a := Fin.ext (h2.trans (C.finRotate_val a).symm)
      rw [hfin] at heq
      have hh := hcausal a
      linarith
    · exact Or.inr (Or.inl ⟨heq.symm, h1, h2⟩)
  · exact Or.inr (Or.inr ⟨hgt, negFlux_eq_leftEdge C hsep hSR hCeven hcausal a b hgt⟩)

/-- **No off-cycle true-reaction class drains any cycle species.**

This is the single named proposition on which the Hole B residue at
`TrueChemistrySRCriterion.lean:8607` depends: it is what forbids the first hop of the minimal
aggregate causal path `Q0` out of the on-cycle species `s0` from landing on an off-cycle class.
DEAD-ENDS B-3 records that `hrest` cannot discharge it (its natural instance is refuted by
`hattachment`); this `no_offCycle_negFlux` is the correctly-scoped replacement. -/
def no_offCycle_negFlux (α : N.fullyOpen.R → ℝ) (σ : S → ℝ) (C : N.TrueSRCycle n) : Prop :=
  ∀ (b : Fin n) (ρ : N.TrueReaction), ¬ C.HasReaction ρ →
    0 ≤ N.trueInternalClassFlux α ρ (C.species b) * σ (C.species b)

/-- **One-step case split out of a cycle species.**  A strictly negative aggregate flux at
`C.species b` comes either from `C.reaction b` itself, or from a class off the cycle.  Under
`no_offCycle_negFlux` the first alternative is forced: *the step lands on `C.reaction b`*. -/
theorem negCausalStep_from_cycleSpecies (C : N.TrueSRCycle n)
    (hsep : N.ReactantProductSeparated) (hSR : N.TrueSRStrongCriterion) (hCeven : C.Even)
    (hcausal : ∀ i : Fin n,
      0 < N.trueInternalClassFlux α (C.reaction i) (C.species (finRotate n i)) *
        σ (C.species (finRotate n i)))
    (hoff : no_offCycle_negFlux α σ C) (b : Fin n) (ρ : N.TrueReaction)
    (h : N.trueInternalClassFlux α ρ (C.species b) * σ (C.species b) < 0) :
    ρ = C.reaction b := by
  by_cases hC : C.HasReaction ρ
  · obtain ⟨t, ht⟩ := hC
    rw [← ht] at h
    rw [← ht]
    exact congrArg C.reaction (negFlux_eq_leftEdge C hsep hSR hCeven hcausal t b h)
  · exact absurd h (not_lt_of_ge (hoff b ρ hC))

/-- Lifting `TrueSRCycle.HasVertex` to the aggregate causal graph's vertex type.  This is the
predicate `hg0` and `hQ0late` are stated with inside `TrueChemistrySRCriterion.lean`, where it is
reached through the `private` map `aggregateVertexToTrueSRVertex` — unreachable from another
module, which is why it is restated here. -/
def aggregateVertexOnCycle (α : N.fullyOpen.R → ℝ) (σ : S → ℝ) (C : N.TrueSRCycle n) :
    N.TrueInternalAggregateVertex α σ → Prop
  | Sum.inl s => C.HasSpecies s.1
  | Sum.inr ρ => C.HasReaction ρ.1

/-- **Conditional discharge of the Hole B residue, Case B.**

A minimal aggregate causal path that starts at a cycle species and whose every other vertex is
off the cycle cannot exist, provided no off-cycle class drains a cycle species.  At the residue
(`TrueChemistrySRCriterion.lean:8579`–`8607`, `cases hv0 … | inl s0`) the situation is exactly this
with `m > 0`, so the residue follows from `no_offCycle_negFlux` alone. -/
theorem no_escape_from_cycleSpecies (C : N.TrueSRCycle n)
    (hsep : N.ReactantProductSeparated) (hSR : N.TrueSRStrongCriterion) (hCeven : C.Even)
    (hcausal : ∀ i : Fin n,
      0 < N.trueInternalClassFlux α (C.reaction i) (C.species (finRotate n i)) *
        σ (C.species (finRotate n i)))
    (hoff : no_offCycle_negFlux α σ C)
    {T : Finset (N.TrueInternalAggregateVertex α σ)} {m : ℕ}
    (Q : CRNT.RelPath (N.TrueInternalAggregateCausalEdge (α := α) (σ := σ)) T m) (hm : 0 < m)
    {s0 : AggregateActiveSpecies σ}
    (hv0 : Q.vertex ⟨0, by omega⟩ = Sum.inl s0) (hs0C : C.HasSpecies s0.1)
    (hlate : ∀ i : Fin (m + 1), i.1 ≠ 0 →
      ¬ aggregateVertexOnCycle α σ C (Q.vertex i)) : False := by
  classical
  obtain ⟨b, hb⟩ := hs0C
  have hstep : N.TrueInternalAggregateCausalEdge
      (Q.vertex ⟨0, by omega⟩ : N.TrueInternalAggregateVertex α σ)
      (Q.vertex (⟨1, by omega⟩ : Fin (m + 1))) := by
    exact Q.step ⟨0, hm⟩
  rw [hv0] at hstep
  cases hv1 : Q.vertex (⟨1, by omega⟩ : Fin (m + 1)) with
  | inl x =>
      have hbad : N.TrueInternalAggregateCausalEdge (α := α) (σ := σ)
          (Sum.inl s0) (Sum.inl x) := by
        rw [hv1] at hstep
        exact hstep
      exact hbad.elim
  | inr ρ1 =>
      have hgood : N.TrueInternalAggregateCausalEdge (α := α) (σ := σ)
          (Sum.inl s0) (Sum.inr ρ1) := by
        rw [hv1] at hstep
        exact hstep
      change N.trueInternalClassFlux α ρ1.1 s0.1 * σ s0.1 < 0 at hgood
      have hρ : ρ1.1 = C.reaction b := by
        rw [← hb] at hgood
        exact negCausalStep_from_cycleSpecies C hsep hSR hCeven hcausal hoff b ρ1.1 hgood
      have hlate1 : ¬ aggregateVertexOnCycle α σ C
          (Q.vertex (⟨1, by omega⟩ : Fin (m + 1))) :=
        hlate (⟨1, by omega⟩ : Fin (m + 1)) (by show (1 : ℕ) ≠ 0; omega)
      refine hlate1 (hv1 ▸ ?_)
      show C.HasReaction ρ1.1
      rw [hρ]
      exact ⟨b, rfl⟩

/-- **The ear's off-cycle end, extracted.**  If `no_offCycle_negFlux` fails, there is an off-cycle
true-reaction class with a strictly negative class flux at some cycle species.  Together with
`hattachment` (which gives an off-cycle class *positive* at another cycle species) this is the
pair of off-cycle endpoints the A.6 Case-2 ear needs; the hypothesis is refutable by nothing in
scope, which is exactly why DEAD-ENDS B-3 lists it as the frontier. -/
theorem exists_offCycle_negFlux_class {n : ℕ} {C : N.TrueSRCycle n}
    (hoff_neg : ¬ no_offCycle_negFlux α σ C) :
    ∃ (b : Fin n) (ρ : N.TrueReaction), ¬ C.HasReaction ρ ∧
      N.trueInternalClassFlux α ρ (C.species b) * σ (C.species b) < 0 := by
  by_contra hnone
  apply hoff_neg
  intro b ρ hρ
  by_contra h
  exact hnone ⟨b, ρ, hρ, not_le.mp h⟩

end TrueSRCycle

end CRNT.Network
