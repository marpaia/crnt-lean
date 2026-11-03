import CRNT.Examples.ReversiblePair
import CRNT.Dynamics.Siphon
import CRNT.Dynamics.GACNoCriticalSiphon
import CRNT.Theorems.DeficiencyZero.Existence
import CRNT.Equilibria.CompatibilityClass

set_option backward.isDefEq.respectTransparency false

/-!
# Global attraction for the reversible pair `A ⇌ B`

A worked instantiation of `gac_of_hasNoCriticalSiphon` on a concrete network. The reversible
pair has no critical siphon — its only nonempty siphon is the full species set `{A, B}`, on
which the total-mass vector `v ≡ 1` is a strictly positive conservation law — so the
no-critical-siphon global-attraction theorem applies to it for every choice of rate
constants. This exhibits a network meeting all hypotheses of the theorem simultaneously.

Depends on:
`CRNT.Examples.ReversiblePair`, `CRNT.Dynamics.Siphon`, `CRNT.Dynamics.GACNoCriticalSiphon`,
`CRNT.Theorems.DeficiencyZero.Existence`, `CRNT.Equilibria.CompatibilityClass`.
-/

namespace CRNT.Examples.ReversiblePair

open CRNT Species
open scoped NNReal

/-- Every nonempty siphon of `A ⇌ B` contains both species. The forward reaction produces
`B` and consumes only `A`, and the backward reaction produces `A` and consumes only `B`, so
membership of either species forces the other. -/
theorem mem_of_siphon (P : Finset Species) (hsiph : N.IsSiphon P) (hne : P.Nonempty) :
    ∀ s : Species, s ∈ P := by
  classical
  have stepA : A ∈ P → B ∈ P := by
    intro hA
    obtain ⟨t, htP, ht⟩ := hsiph Rxn.bwd ⟨A, hA, by decide⟩
    cases t with
    | A => exact absurd ht (by decide)
    | B => exact htP
  have stepB : B ∈ P → A ∈ P := by
    intro hB
    obtain ⟨t, htP, ht⟩ := hsiph Rxn.fwd ⟨B, hB, by decide⟩
    cases t with
    | A => exact htP
    | B => exact absurd ht (by decide)
  obtain ⟨s, hs⟩ := hne
  have hAB : A ∈ P ∧ B ∈ P := by
    cases s with
    | A => exact ⟨hs, stepA hs⟩
    | B => exact ⟨stepB hs, hs⟩
  intro s; cases s
  · exact hAB.1
  · exact hAB.2

/-- The reaction vectors of `A ⇌ B` are mass-conserving: their species sum vanishes. -/
theorem sum_reactionVector (r : Rxn) : ∑ s : Species, N.reactionVector r s = 0 := by
  have huniv : (Finset.univ : Finset Species) = {A, B} := by decide
  rw [huniv, Finset.sum_pair (show (A : Species) ≠ B by decide)]
  cases r <;>
    simp [Network.reactionVector, N, rxn, Reaction.vector, cA, cB]

/-- **The reversible pair has no critical siphon.** Any nonempty siphon is the full species
set, and the total-mass vector `v ≡ 1` is strictly positive there and orthogonal to every
reaction vector, so it witnesses that no subset is a critical siphon. -/
theorem hasNoCriticalSiphon : N.HasNoCriticalSiphon := by
  intro P hcrit
  obtain ⟨hne, hsiph, hnov⟩ := hcrit
  have hmem := mem_of_siphon P hsiph hne
  exact hnov ⟨fun _ => 1, fun _ => zero_le_one, fun s => iff_of_true one_pos (hmem s),
    fun r => by simpa using sum_reactionVector r⟩

/-- **Global attraction for the reversible pair.** For every rate constants `κ` there is a
positive complex-balanced equilibrium whose mass-action orbit converges to it: all
hypotheses of `gac_of_hasNoCriticalSiphon` hold for this network, so its conclusion fires. -/
theorem gac_reversiblePair (κ : N.RateConstants) :
    ∃ xstar : Concentration Species, xstar.Positive ∧ N.IsComplexBalanced κ xstar ∧
      ∃ (ϕ : Flow ℝ≥0 (Concentration Species))
        (γ : Concentration Species → ℝ → Concentration Species),
        (∀ x, γ x 0 = x) ∧ (∀ x (t : ℝ≥0), ϕ t x = γ x t) ∧
        (∀ t, 0 ≤ t → HasDerivAt (γ xstar) (N.massActionVectorField κ (γ xstar t)) t) ∧
        omegaLimit Filter.atTop ϕ {xstar} = {xstar} := by
  obtain ⟨xstar, hpos, hcb⟩ := N.exists_isComplexBalanced weaklyReversible deficiencyZero κ
  obtain ⟨ϕ, γ, hγ0, hϕγ, hderiv, hω⟩ :=
    N.gac_of_hasNoCriticalSiphon weaklyReversible κ hasNoCriticalSiphon hpos hcb hpos
      (Network.StoichCompatible.refl N xstar)
  exact ⟨xstar, hpos, hcb, ϕ, γ, hγ0, hϕγ, hderiv, hω⟩

end CRNT.Examples.ReversiblePair
