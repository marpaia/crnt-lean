import Mathlib.Tactic.DeriveFintype
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import CRNT.Basic.Complex
import CRNT.Basic.Reaction
import CRNT.Basic.Network
import CRNT.Stoich.Vector
import CRNT.Stoich.Subspace
import CRNT.Graph.Reachability
import CRNT.Graph.WeakReversibility
import CRNT.Graph.LinkageClass
import CRNT.Deficiency.Definition
import CRNT.Theorems.DeficiencyZero.Statement
import CRNT.Equilibria.WegscheiderConverse

/-!
# Reversible pair `A ⇌ B`

The canonical deficiency-zero network. It has two species, two complexes, two
reactions, one linkage class, and stoichiometric rank one, hence deficiency
`δ = 2 - 1 - 1 = 0`. This module proves all of these, including weak reversibility and
deficiency zero.
-/

namespace CRNT.Examples.ReversiblePair

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

/-- The network `A ⇌ B`. -/
def N : Network Species :=
  { R := Rxn, decEqR := inferInstance, fintypeR := inferInstance, reaction := rxn }

theorem cA_ne_cB : cA ≠ cB := by decide

/-- `n = 2`: the network has two complexes. -/
theorem numComplexes_eq : N.numComplexes = 2 := by decide

/-- The network has two reaction channels. -/
theorem numReactions_eq : N.numReactions = 2 := by decide

/-- The complexes of the network are exactly `{A, B}`. -/
theorem complexes_eq : N.complexes = {cA, cB} := by decide

/-- The network is weakly reversible: each reaction has an explicit return reaction. -/
theorem weaklyReversible : N.WeaklyReversible := by
  intro r
  cases r
  · exact Network.Reaches.single ⟨Rxn.bwd, rfl, rfl⟩
  · exact Network.Reaches.single ⟨Rxn.fwd, rfl, rfl⟩

/-- The forward reaction vector is `B - A`. -/
theorem reactionVector_fwd :
    N.reactionVector .fwd = fun s => match s with | A => (-1 : ℝ) | B => 1 := by
  funext s
  cases s <;> simp [Network.reactionVector, N, rxn, Reaction.vector, cA, cB]

theorem reactionVector_fwd_ne_zero : N.reactionVector .fwd ≠ 0 := by
  intro h
  have := congrFun h Species.A
  simp [Network.reactionVector, N, rxn, Reaction.vector, cA, cB] at this

/-- Every complex is linked to `A`, so the undirected reaction graph is connected. -/
theorem linked_cA : ∀ c ∈ N.complexes, N.Linked c cA := by
  intro c hc
  rw [complexes_eq] at hc
  simp only [Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with rfl | rfl
  · exact Network.Linked.refl N cA
  · exact Relation.ReflTransGen.single (Or.inl ⟨Rxn.bwd, rfl, rfl⟩)

/-- `ℓ = 1`: there is a single linkage class. -/
theorem numLinkageClasses_eq : N.numLinkageClasses = 1 := by
  have hss : Subsingleton (Quotient N.linkedSetoid) := by
    refine ⟨fun q q' => ?_⟩
    induction q using Quotient.inductionOn with
    | _ a =>
      induction q' using Quotient.inductionOn with
      | _ b =>
        exact Quotient.sound
          ((linked_cA a.val a.2).trans (linked_cA b.val b.2).symm)
  have hne : Nonempty (Quotient N.linkedSetoid) :=
    ⟨Quotient.mk _ ⟨cA, N.source_mem_complexes Rxn.fwd⟩⟩
  exact Nat.card_eq_one_iff_unique.mpr ⟨hss, hne⟩

/-- `s = 1`: the stoichiometric subspace is the line spanned by the forward reaction
vector. -/
theorem stoichRank_eq : N.stoichRank = 1 := by
  have hbwd : N.reactionVector Rxn.bwd = -N.reactionVector Rxn.fwd := by
    funext s
    cases s <;> simp [Network.reactionVector, N, rxn, Reaction.vector, cA, cB]
  have hsub : N.stoichSubspace = Submodule.span ℝ {N.reactionVector Rxn.fwd} := by
    apply le_antisymm
    · apply Submodule.span_le.2
      rintro x ⟨r, rfl⟩
      cases r
      · exact Submodule.subset_span rfl
      · rw [hbwd]
        exact Submodule.neg_mem _ (Submodule.subset_span rfl)
    · apply Submodule.span_le.2
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact N.reactionVector_mem_stoichSubspace Rxn.fwd
  rw [Network.stoichRank, hsub, finrank_span_singleton reactionVector_fwd_ne_zero]

/-- **Deficiency zero**: `δ = n - ℓ - s = 2 - 1 - 1 = 0`. -/
theorem deficiencyZero : N.DeficiencyZero := by
  rw [Network.deficiencyZero_iff_eq, numComplexes_eq, numLinkageClasses_eq, stoichRank_eq]

/-- The network satisfies the structural hypotheses of the deficiency-zero theorem. -/
theorem satisfiesDeficiencyZeroHypotheses : N.SatisfiesDeficiencyZeroHypotheses :=
  ⟨weaklyReversible, deficiencyZero⟩

/-! ## Detailed balance: a non-vacuity witness

`ReversibleStructure` and `IsDetailedBalanced` are quantified predicates, and such a predicate can
be accidentally unsatisfiable, or accidentally trivial, with no error appearing. This repository
has already produced one such defect: `FloquetOrbitalStabilityTarget` asked only for *some* basin
containing the orbit, satisfied by taking the basin to be the orbit itself, so it said nothing.

The results below rule that out for the detailed-balance layer: this network carries a reversible
structure, and it has a positive concentration that is detailed balanced -- hence, by
`IsDetailedBalanced.isComplexBalanced` and `IsComplexBalanced.isSteadyState`, all three predicates
of the classical chain are simultaneously satisfiable on a concrete network. -/

/-- Products over the two-element species type expand to a single multiplication. `Species` is a
derived-`Fintype` inductive, so neither `Finset.prod_univ_two` nor `decide` applies directly. -/
theorem prod_univ_species (f : Species → ℝ) : (∏ s : Species, f s) = f A * f B := by
  have huniv : (Finset.univ : Finset Species) = {A, B} := by decide
  rw [huniv, Finset.prod_insert (by decide), Finset.prod_singleton]

/-- Swapping the two channels exchanges source and target, so `A ⇌ B` carries a reversible
pairing. -/
def revStruct : Network.ReversiblePairing N where
  rev := fun r => match r with | .fwd => .bwd | .bwd => .fwd
  involutive := by intro r; cases r <;> rfl
  source_rev := by intro r; cases r <;> rfl
  target_rev := by intro r; cases r <;> rfl

/-- Rate constants: `k₀` forward, `k₁` backward. -/
def rates {k₀ k₁ : ℝ} (h₀ : 0 < k₀) (h₁ : 0 < k₁) : Network.RateConstants N where
  k := fun r => match r with | .fwd => k₀ | .bwd => k₁
  positive := by intro r; cases r <;> assumption

/-- The equilibrium concentration `(k₁, k₀)`: reciprocal to the rate constants, which is the
detailed-balance condition for a single reversible pair. -/
def equilibrium (k₀ k₁ : ℝ) : Concentration Species :=
  fun s => match s with | A => k₁ | B => k₀

/-- The equilibrium concentration is strictly positive. -/
theorem equilibrium_positive {k₀ k₁ : ℝ} (h₀ : 0 < k₀) (h₁ : 0 < k₁) :
    (equilibrium k₀ k₁).Positive := by
  intro s
  cases s
  · exact h₁
  · exact h₀

/-- **The witness.** At `(k₁, k₀)` the forward flux `k₀ · k₁` and the reverse flux `k₁ · k₀`
coincide, so the concentration is detailed balanced. -/
theorem equilibrium_isReactionwiseDetailedBalanced {k₀ k₁ : ℝ} (h₀ : 0 < k₀) (h₁ : 0 < k₁) :
    N.IsReactionwiseDetailedBalanced revStruct (rates h₀ h₁) (equilibrium k₀ k₁) := by
  intro r
  cases r <;>
    simp [Network.massActionRate, Complex.massActionMonomial, revStruct, rates, equilibrium,
      N, rxn, cA, cB, prod_univ_species] <;>
    ring

/-- Hence the equilibrium is complex balanced -- the first link of the chain, on a concrete
network. -/
theorem equilibrium_isComplexBalanced {k₀ k₁ : ℝ} (h₀ : 0 < k₀) (h₁ : 0 < k₁) :
    N.IsComplexBalanced (rates h₀ h₁) (equilibrium k₀ k₁) :=
  N.isComplexBalanced_of_isDetailedBalanced _ _
    (N.isDetailedBalanced_of_reactionwiseDetailedBalanced revStruct _ _
      (equilibrium_isReactionwiseDetailedBalanced h₀ h₁))

/-- And hence a genuine steady state of the mass-action dynamics -- the second link. -/
theorem equilibrium_isSteadyState {k₀ k₁ : ℝ} (h₀ : 0 < k₀) (h₁ : 0 < k₁) :
    N.IsMassActionSteadyState (rates h₀ h₁) (equilibrium k₀ k₁) :=
  (equilibrium_isComplexBalanced h₀ h₁).isMassActionSteadyState N _

/-- **The Wegscheider layer is non-vacuous.** `SatisfiesWegscheider` and
`HasWegscheiderPotential` are quantified predicates over an orthogonal complement; this shows
the concrete network `A ⇌ B` satisfies them for every choice of positive rate constants, via the
detailed-balanced point exhibited above. -/
theorem satisfiesWegscheider {k₀ k₁ : ℝ} (h₀ : 0 < k₀) (h₁ : 0 < k₁) :
    N.SatisfiesWegscheider revStruct (rates h₀ h₁) :=
  N.satisfiesWegscheider_of_reactionwiseDetailedBalanced revStruct (rates h₀ h₁)
    (equilibrium_positive h₀ h₁) (equilibrium_isReactionwiseDetailedBalanced h₀ h₁)

/-- Hence the species potential exists too, closing the loop on the equivalence in
`WegscheiderConverse` for a concrete network. -/
theorem hasWegscheiderPotential {k₀ k₁ : ℝ} (h₀ : 0 < k₀) (h₁ : 0 < k₁) :
    N.HasWegscheiderPotential revStruct (rates h₀ h₁) :=
  (N.satisfiesWegscheider_iff_hasWegscheiderPotential revStruct (rates h₀ h₁)).mp
    (satisfiesWegscheider h₀ h₁)

end CRNT.Examples.ReversiblePair
