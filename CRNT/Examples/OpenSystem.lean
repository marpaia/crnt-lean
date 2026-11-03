import CRNT.Open.Augmentation
import CRNT.Examples.ReversiblePair
import CRNT.Equilibria.CompatibilityClass
import CRNT.Theorems.DeficiencyZero.Existence

/-!
# The fully open extension of the reversible pair `A ⇌ B`

Exercises the open-network construction. Adjoining a synthesis and degradation for each of
the two species turns the rank-one closed network into a fully open one whose
stoichiometric subspace is all of `Species → ℝ` (rank `2`) and which has no nontrivial
conservation law.

The second half of this module is a counterexample to a packaging hypothesis of the barrier
criteria in `CRNT.Dynamics.ToricBarrierExplicit`: those criteria assume
`hMclass : ∀ x, x.Positive → N.StoichCompatible x₀ x → ∀ u, x u ≤ M`, a uniform bound on the
**whole positive compatibility class**.  The network below is weakly reversible of deficiency
zero — hence complex balanced for *every* rate vector, so it satisfies the standing hypotheses
`hxs`/`hcb` of `CRNT.Network.exists_positive_omegaPoint_of_highCodimension_siphonFace` — and its
stoichiometric subspace is everything, so its positive compatibility classes are the whole
positive orthant and `hMclass` fails for every `M`.  Craciun's paper never assumes bounded
compatibility classes (his compact region is bounded by the cube `[0,M]ⁿ` containing the
*trajectory* together with a level set of the Horn–Jackson Lyapunov function, v3 §6.1/§9.4), so
`hMclass` is an extra hypothesis of the repo's packaging, not a consequence of the paper's
standing assumptions.
-/

namespace CRNT.Examples.OpenSystem

open CRNT CRNT.Examples.ReversiblePair

/-- The fully open extension of `A ⇌ B`. -/
def Nopen : Network Species := N.fullyOpen

/-- There are two species. -/
theorem card_species : Fintype.card Species = 2 := by decide

/-- Opening the network raises the stoichiometric rank to `2`: the closed network had
rank one (one conservation law `[A] + [B]`); the open one has full rank. -/
theorem stoichRank_open : Nopen.stoichRank = 2 := by
  rw [Nopen, N.stoichRank_fullyOpen, card_species]

/-- The open extension's stoichiometric subspace is everything. -/
example : Nopen.stoichSubspace = ⊤ :=
  N.stoichSubspace_fullyOpen_eq_top

/-- The open extension has no nontrivial conservation law. -/
example : orthSum Nopen.stoichSubspace = ⊥ :=
  N.orthSum_stoichSubspace_fullyOpen_eq_bot

/-! ## The open extension is weakly reversible of deficiency zero, hence complex balanced -/

/-- The complexes of the fully open extension are `A`, `B` and the zero complex. -/
theorem complexes_open : Nopen.complexes = {cA, cB, Complex.zero} := by decide

/-- The inflow target `singletonComplex A` is definitionally the complex `A` written
componentwise. -/
theorem singletonComplex_A : singletonComplex Species.A = cA := by
  funext s
  cases s <;> simp [singletonComplex_apply, cA]

/-- Every complex of the open extension is linked to `A`: `A ⇌ B` links `B`, and the
inflow `0 → A` links the zero complex. -/
theorem linked_cA_open : ∀ c ∈ Nopen.complexes, Nopen.Linked c cA := by
  intro c hc
  rw [complexes_open] at hc
  simp only [Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with rfl | rfl | rfl
  · exact Network.Linked.refl Nopen cA
  · exact Relation.ReflTransGen.single (Or.inl ⟨Sum.inl Rxn.bwd, rfl, rfl⟩)
  · exact Relation.ReflTransGen.single
      (Or.inl ⟨Sum.inr (Sum.inl Species.A), rfl, singletonComplex_A⟩)

/-- `ℓ = 1`: the open extension still has a single linkage class. -/
theorem numLinkageClasses_open : Nopen.numLinkageClasses = 1 := by
  have hss : Subsingleton (Quotient Nopen.linkedSetoid) := by
    refine ⟨fun q q' => ?_⟩
    induction q using Quotient.inductionOn with
    | _ a =>
      induction q' using Quotient.inductionOn with
      | _ b =>
        exact Quotient.sound
          ((linked_cA_open a.val a.2).trans (linked_cA_open b.val b.2).symm)
  have hne : Nonempty (Quotient Nopen.linkedSetoid) :=
    ⟨Quotient.mk _ ⟨cA, Nopen.source_mem_complexes (Sum.inl Rxn.fwd)⟩⟩
  exact Nat.card_eq_one_iff_unique.mpr ⟨hss, hne⟩

/-- `n = 3`: three complexes, `A`, `B` and `0`. -/
theorem numComplexes_open : Nopen.numComplexes = 3 := by decide

/-- **Deficiency zero**: `δ = n - ℓ - s = 3 - 1 - 2 = 0`. -/
theorem deficiencyZero_open : Nopen.DeficiencyZero := by
  rw [Network.deficiencyZero_iff_eq, numComplexes_open, numLinkageClasses_open, stoichRank_open]

/-- The open extension is weakly reversible: the closed pair returns through its own
channel, and each inflow returns through the matching outflow. -/
theorem weaklyReversible_open : Nopen.WeaklyReversible := by
  intro r
  cases r with
  | inl r =>
    cases r
    · exact Network.Reaches.single ⟨Sum.inl Rxn.bwd, rfl, rfl⟩
    · exact Network.Reaches.single ⟨Sum.inl Rxn.fwd, rfl, rfl⟩
  | inr s =>
    cases s with
    | inl sp =>
      cases sp
      · exact Network.Reaches.single ⟨Sum.inr (Sum.inr Species.A), rfl, rfl⟩
      · exact Network.Reaches.single ⟨Sum.inr (Sum.inr Species.B), rfl, rfl⟩
    | inr sp =>
      cases sp
      · exact Network.Reaches.single ⟨Sum.inr (Sum.inl Species.A), rfl, rfl⟩
      · exact Network.Reaches.single ⟨Sum.inr (Sum.inl Species.B), rfl, rfl⟩

/-- Weak reversibility plus deficiency zero: the open extension satisfies the structural
hypotheses of the deficiency-zero theorem. -/
theorem satisfiesDeficiencyZeroHypotheses_open :
    Nopen.SatisfiesDeficiencyZeroHypotheses :=
  ⟨weaklyReversible_open, deficiencyZero_open⟩

/-- **A positive complex-balanced equilibrium exists for every rate vector** (deficiency
zero + weak reversibility). -/
theorem exists_complexBalanced_open (κ : Nopen.RateConstants) :
    ∃ xstar : Concentration Species, xstar.Positive ∧ Nopen.IsComplexBalanced κ xstar :=
  Nopen.exists_isComplexBalanced weaklyReversible_open deficiencyZero_open κ

/-! ## `hMclass` is not available in this setting -/

/-- **`hMclass` fails on the open extension, for every level `M`.**  The stoichiometric
subspace is all of `Species → ℝ`, so *every* positive concentration is stoichiometrically
compatible with `x₀`, and the positive compatibility class is the whole positive orthant —
unbounded.  Explicitly, the constant concentration `max M 0 + 1` is positive, compatible,
and exceeds `M` at every species. -/
theorem not_hMclass_open (x₀ : Concentration Species) (M : ℝ) :
    ¬ ∀ x : Concentration Species, x.Positive → Nopen.StoichCompatible x₀ x →
      ∀ u : Species, x u ≤ M := by
  intro h
  let big : Concentration Species := fun _ => max M 0 + 1
  have hypos : big.Positive := by
    intro u
    show 0 < max M 0 + 1
    linarith [le_max_right M 0]
  have hcompat : Nopen.StoichCompatible x₀ big := by
    have hmem : big - x₀ ∈ N.fullyOpen.stoichSubspace := by
      rw [N.stoichSubspace_fullyOpen_eq_top]
      exact Submodule.mem_top
    exact hmem
  have hle := h big hypos hcompat Species.A
  change max M 0 + 1 ≤ M at hle
  linarith [le_max_left M 0]

/-- **Packaging finding, packaged.**  There is a network with a positive complex-balanced
equilibrium — exactly the standing hypotheses `hxs`/`hcb` of the residual GAC obligation —
whose positive compatibility classes are unbounded, so the `hMclass` hypothesis of
`Network.exists_positive_omegaPoint_of_blueprintData` is *not* derivable from those
hypotheses.  Craciun's construction never uses it: the outer bound in v3 comes from the cube
`[0,M]ⁿ` around the (bounded) trajectory together with a level set of the Horn–Jackson
Lyapunov function (v3 §6.1, §9.4 Lemma 9.11), i.e. it bounds the invariant *region*, not the
compatibility class. -/
theorem exists_complexBalanced_unbounded_class (κ : Nopen.RateConstants) :
    ∃ xstar : Concentration Species, xstar.Positive ∧ Nopen.IsComplexBalanced κ xstar ∧
      ∀ (x₀ : Concentration Species) (M : ℝ),
        ¬ ∀ x : Concentration Species, x.Positive → Nopen.StoichCompatible x₀ x →
          ∀ u : Species, x u ≤ M := by
  obtain ⟨xstar, hxs, hcb⟩ := exists_complexBalanced_open κ
  exact ⟨xstar, hxs, hcb, not_hMclass_open⟩

end CRNT.Examples.OpenSystem
